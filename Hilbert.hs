{-# OPTIONS_GHC -fglasgow-exts #-}

import Text.PrettyPrint.HughesPJ hiding((<>))
import Control.Monad.Reader
import Control.Monad
import Control.Exception
import Data.List
import Numeric
import Data.Char
import Data.Monoid
import Data.IORef
import Data.Bits
import System.IO

hasUnicode = True

type Id = String
data Term
    = Bound !Int
    | Constant Id
    | Function Id Term
    | Pair Term Term
    | TVar (UVar Term)
    deriving(Eq)

data Formula
    = Forall Formula
    | Formula :-> Formula
    | Formula :<> Formula
    | Not Formula
    | QPred (UWrap Id) Term
    | Pred String Term
    | Term := Term
    | FVar (UVar Formula)
    deriving(Eq)

data HState = HState { stateFormula :: [Formula], stateAxioms :: [Formula] } deriving(Eq)
stateEmpty = HState { stateAxioms = reverse (axioms ++ hypo), stateFormula = []  }

main = do
    --search $ axioms  ++ hypo -- (take 3 axioms)
    hSetBuffering stdin NoBuffering
    loop (repeat stateEmpty) ""

perform 'h' ss = do
    putStr clearScreen
    putStr help
    putStrLn "-----"
    getChar
    loop ss ""
perform 'u' (_:ss) = loop ss ""
perform c (s:ss) | isUpper c = case lookup c (zip ['A' ..] (reverse $ stateAxioms s)) of
    Just a -> loop (s { stateFormula = a:stateFormula s }:s:ss) ""
    Nothing -> loop (s:ss) "Unknown Formula"
perform c (s:ss) | isDigit c && c > '0' = do
    let idx = ord c - ord '0';
        f 0 (x:xs) rs = loop (s { stateFormula = x:(reverse rs ++ xs) }:s:ss) ""
        f n (x:xs) rs = f (n - 1) xs (x:rs)
        f n [] _ = loop (s:ss) "Not in stack"
    f idx (stateFormula s) []
perform c (s:ss) = f c s where
--    f 's' s@HState { stateFormula = (x:y:rs) } = next s { stateFormula = (y:x:rs) }
    f '0' s@HState { stateFormula = (x:rs) } = next s { stateFormula = (x:x:rs) }
    f '-' s@HState { stateFormula = (x:rs) } = next s { stateFormula = rs }
    f 'd' s@HState { stateFormula = (x:rs) } = degen s rs x
    f 'g' s@HState { stateFormula = (x:rs) } = gen s rs x
    f 'p' s@HState { stateFormula = (x:rs) } | x `notElem` stateAxioms s = next s { stateFormula = rs, stateAxioms = x:stateAxioms s }
                                             | otherwise = err "Formula Already Exists."
    f 'm' s@HState { stateFormula = (x:y:rs) } = modus_p s rs x y
    f '!' _ = return ()
    f '\ESC' _ = return ()
    f '\x04' _ = return ()
    f c s = err $ "Unknown Command " ++ show c
    next x = if x /= s then loop (x:s:ss) "" else loop (s:ss) ""
    err x = loop (s:ss) x
    --modus_p s rs (p :-> q) p' | p' == p = next s { stateFormula = q:rs }
    modus_p s rs (p :<> q) p' = do
        mp <- modus_pones p q p'
        case mp of
            Just q' ->  next s { stateFormula = q':rs }
            Nothing -> modus_p s rs (q :-> p) p'
    modus_p s rs (p :-> q) p' = do
        mp <- modus_pones p q p'
        case mp of
            Just q' ->  next s { stateFormula = q':rs }
            Nothing -> err "Modus Pones didn't unify"
    modus_p _ _ _ _ = err "Could not perform modus_pones"
    degen s rs (Forall x) = next  s { stateFormula = rmap 1 (TVar (UGen nt)) x:rs }  where
        (_,ts) = freeVars x
        nt :: Int
        nt = head [ c | c <- [ 0 .. ], UGen c `notElem` ts]
    degen _ _ _ = err "Could not degeneralize"
    gen s rs x | not (null ts) = next  s { stateFormula = foldr (\_ -> Forall) (bmap (zip ts [1 ..]) x) ts:rs }  where
        ts = nub $ snd $ freeVars x
    gen _ _ _ = err "nothing to generalize"
    bmap m x = f m x where
        f m (Forall x) = Forall (f [ (x,y + 1) | (x,y) <- m ] x)
        f m x = formMap (f m) (g m) x
        g m (TVar z) | Just x <- lookup z m  = Bound x
        g m x = termMap (g m) x
    rmap n w x = f n x where
        f n (Forall x) = Forall $ f (n + 1) x
        f n x = formMap (f n) (g n) x
        g n (Bound z) | z == n = w
        g n x = termMap (g n) x

clearScreen = "\x1b[H\x1b[2J"

loop ss@(s:_) msg = do
    putStr clearScreen
    putStrLn "press 'h' for help\n---- Axioms"
    let pa c a = [c] ++ ". " ++ show a
        la = length axioms
    mapM_ putStrLn (zipWith pa ['a' .. ] (take la . reverse $ stateAxioms s))
    putStr "---- Hypothesis\n"

    mapM_ putStrLn (drop la $ zipWith pa ['a' .. ] (reverse $ stateAxioms s))
    putStr "---- Stack\n"
    mapM_ putStrLn (reverse $ zipWith pa ['0' ..] (stateFormula s))
    handle (\ (e :: SomeException) -> return ()) $ do
        (p :-> q:p':_) <- return $ stateFormula s
        Just res <- modus_pones p q p'
        putStr $ "----\n" ++ msg
        putStrLn $ "m. " ++ show res
    putStr $ "----\n" ++ msg
    hFlush stdout
    gl <- getChar
    putStrLn []
    perform gl ss


freeVars x = f x where
    f (FVar v) = ([v],[])
    f (Pred _ ts) = ([],g ts)
    f (QPred _ ts) = ([],g ts)
    f (a := b) = ([],g a ++ g b)
    f x = formCollect f x
    g (TVar t) = [t]
    g (Function _ ts) = g ts
    g (Pair a b) = g a ++ g b
    g _ = []

modus_pones :: Formula -> Formula -> Formula -> IO (Maybe Formula)
modus_pones p q p' = ans where
    ans = do
        (p :-> q) <- uvarIze (p :-> q)
        p' <- uvarIze p'
        let fn = do
            unify p p'
            deUVar q
--        fmap Just fn
        catch (fmap Just fn) (\ (e::SomeException) -> (return Nothing))

    unify :: Formula -> Formula -> IO ()
    unify x y = join $ return f `ap` (sfindVal x) `ap` (sfindVal y) where
        sfindVal x = do
            x <- findVal x
            case x of
                QPred qp t -> do
                    qp <- findVal qp
                    case qp of
                        UJust s -> return (Pred s t)
                        _ -> return x
                _ -> return x

        f :: Formula -> Formula -> IO ()
        f (FVar x) y = varBind x y
        f x (FVar y) = varBind y x
        f (Pred s ts1)(QPred qp2 ts2) = do
            qp2 <- findVal qp2
            case qp2 of
                UVar ref -> varBind ref (UJust s) >> g' ts1 ts2
                UJust x -> unify (Pred s ts1) (Pred x ts2)
        f (QPred qp1 ts1) (Pred s ts2) = do
            qp1 <- findVal qp1
            case qp1 of
                UVar ref -> varBind ref (UJust s) >> g' ts1 ts2
                UJust x -> unify (Pred x ts1) (Pred s ts2)
        f (QPred qp1 ts1) (QPred qp2 ts2) = do
            qp1 <- findVal qp1
            qp2 <- findVal qp2
            case (qp1,qp2) of
                (UJust x,UJust y) -> unify (Pred x ts1) (Pred y ts2)
                (UJust x,y) -> unify (Pred x ts1) (QPred y ts2)
                (x,UJust y) -> unify (QPred x ts1) (Pred y ts2)
                (UVar a,b) -> varBind a b >> g' ts1 ts2
        f x y = match_ unify g' x y
        g,g' :: Term -> Term -> IO ()
        g' x y = join $ return g `ap` findVal x `ap` findVal y
        g (TVar x) y = varBind x y
        g x (TVar y) = varBind y x
        g (Function s1 ts1) (Function s2 ts2) | s1 == s2 = (g' ts1 ts2)
        g (Pair a b) (Pair c d) = g' a c >> g' b d
        g x y = if x == y then return () else fail "terms don't match"


    deUVar x = do
        dm <- varDestantiator
        tm <- varDestantiator
        ss <- varDestantiator
        let f (QPred s t) = return QPred `ap` ss s `ap` g t
            f x = dm x >>= formMapM f g
            g x = tm x >>= termMapM g
        f x

    uvarIze x = do
        fs <- varInstantiator
        ts <- varInstantiator
        ss <- varInstantiator
        let f (FVar v) = do FVar `fmap` fs v
--            f (QPred qv t) = do return QPred `ap` ss qv `ap` g t
            f x = formMapM f g x
            g (TVar v) = TVar `fmap` ts v
            g x = termMapM g x
        f x

---------------
-- unification
---------------

varBind uv t | Just uv == getUVar t = return ()
varBind uv@(URef ref) t = do
    let occursCheck t = findVal t >>= f where
            f a | Just uv == getUVar a = fail "occurs check"
            f a = smapM occursCheck a
    t <- occursCheck t
    writeIORef ref (Just t)

data UWrap t = UJust t | UVar (UVar (UWrap t))
            deriving(Eq)
data UVar t = URef (IORef (Maybe t))
            | UGen !Int
            deriving(Eq)


newUVar = fmap URef $ newIORef Nothing


varInstantiator :: IO (UVar t -> IO (UVar t))
varInstantiator = do
    vs <- newUVarSource
    let f (UGen i) = vs i
        f _ = fail "varInstantiator, non UGen"
    return f

varDestantiator :: GetUVar t => IO (t -> IO t)
varDestantiator = do
    dm <- newIORef (map UGen [0..])
    let f t = do t' <- findVal t ; g t'
        g tt = case getUVar tt of
            Just (URef ref) -> do
                    (nn:nns) <- readIORef dm
                    writeIORef dm nns
                    varBind (URef ref) (fromUVar nn)
                    return (fromUVar nn)
            _ -> return tt
    return f


newUVarSource :: IO (Int -> IO (UVar a))
newUVarSource = do
    uv <- newIORef []
    let f n = readIORef uv >>= g n []
        g 0 _ (x:_) = return x
        g n rs (x:xs) = g (n - 1) (x:rs) xs
        g n rs [] = do
            u <- newUVar
            if n == 0 then do
                writeIORef uv (reverse $ u:rs)
                return u
             else g (n - 1) (u:rs) []
    return f

class GetUVar a where
    getUVar :: a -> Maybe (UVar a)
    fromUVar :: UVar a -> a
    smapM :: Monad m => (a -> m a) -> a -> m a

instance GetUVar (UWrap t) where
    getUVar (UVar v) = Just v
    getUVar _ = Nothing
    smapM f t = return t
    fromUVar = UVar

instance GetUVar Term where
    getUVar (TVar v) = Just v
    getUVar _ = Nothing
    smapM f t = termMapM f t
    fromUVar = TVar

instance GetUVar Formula where
    getUVar (FVar v) = Just v
    getUVar _ = Nothing
    smapM f p = formMapM f return p
    fromUVar = FVar

findVal :: GetUVar a => a -> IO a
findVal a = ans where
    ans = case getUVar a of
        Just (URef ref) -> f ref
        _ -> return a
    f ref = do
        v <- readIORef ref
        case v of
            Nothing -> return a
            Just t -> do
                t' <- findVal t
                writeIORef ref (Just t')
                return t'

match_ fn pm f1 f2 = f f1 f2 where
    f (Forall x) (Forall y) =  fn x y
    f (x :-> y) (a :-> b) = fn x a >> fn y b
    f (x := y) (a := b) = pm x a >> pm y b
    f (Not f1)  (Not f2)  = fn f1 f2
    f (Pred s1 ts1) (Pred s2 ts2) | s1 == s2 = (pm ts1 ts2)
    f _ _ = fail "match: formulas don't match"

formCollect :: Monoid a => (Formula -> a) -> Formula -> a
formCollect fn x = f x where
    f (Forall a) = fn a
    f (a :-> b) = fn a `mappend` fn b
    f (Not a)   = fn a
    f _ = mempty

formMapM :: Monad m => (Formula -> m Formula) -> (Term -> m Term) -> Formula -> m Formula
formMapM f _ (Forall a) = liftM Forall (f a)
formMapM f _ (a :-> b) = liftM2 (:->) (f a) (f b)
formMapM f _ (Not a)   = liftM Not (f a)
formMapM _ g (Pred s ts) = liftM (Pred s) (g ts)
formMapM _ g (QPred s ts) = liftM (QPred s) (g ts)
--formMapM _ g (QUVar s ts) = liftM (QUVar s) (mapM g ts)
--formMapM _ g (QVar s ts) = liftM (QVar s) (mapM g ts)
formMapM _ g (a := b) = liftM2 (:=) (g a) (g b)
formMapM _ _ x = return x

termMap f (Function s ts) = Function s (f ts)
termMap f (Pair a b) = Pair (f a) (f b)
termMap _ t = t

termMapM f (Function s ts) = return (Function s) `ap` f ts
termMapM f (Pair a b) = return Pair `ap` (f a) `ap` (f b)
termMapM _ t = return t

formMap :: (Formula -> Formula) -> (Term -> Term) -> Formula -> Formula
formMap f _ (Forall a) = Forall (f a)
formMap f _ (a :-> b) = (f a :-> f b)
formMap f _ (Not a)   = Not $ f a
formMap _ g (Pred s ts) = Pred s $ g ts
formMap _ g (QPred s ts) = QPred s $ g ts
--formMap _ g (QUVar s ts) = QUVar s $ map g ts
formMap _ g (a := b) = g a := g b
formMap _ _ x = x


--peq a b = a := b
peq a b = Pred "=" (Pair a b)
b1 = Bound 1
b2 = Bound 2
b3 = Bound 3

fA = FVar (UGen 0)
fB = FVar (UGen 1)
fC = FVar (UGen 2)

s x = Function "S" x
n x = Pred "N" x
zero = Constant "0"

axioms = [
    fA :-> (fB :-> fA),
    (fA :-> (fB :-> fC)) :-> ((fA :-> fB) :-> (fA :-> fC)),
    (Not fA :-> Not fB) :-> (fB :-> fA),
--    fA :-> Not (Not fA),
--    Not (Not fA) :-> fA,
    Forall (fA :-> fB) :-> (Forall fA :-> Forall fB),
    fA :-> Forall fA
    ]

symmetries = [
   (fA :<> fB) :-> (fB :<> fA),                -- TT, FF
   (Not fA :-> fB) :-> (Not fB :-> fA),        -- or
   (fA :-> Not fB) :-> (fB :-> Not fA),        -- nand
   Not (fA :-> Not fB) :-> Not (fB :-> Not fA) -- and
    ]

qp0 = QPred (UVar (UGen 0))


{-



T       denotes (p0 ⇒ p0).
F       denotes (¬T).
(A ∨ B) denotes ((¬A) ⇒ B).
(A ∧ B) denotes (¬((¬A) ∨ (¬B))).
(A ⇔ B) denotes ((A ⇒ B) ∧ (B ⇒ A)).
(A | B) denotes (¬(A ∧ B)).

-}

a /\ b = Not (Not a \/ Not b)
a \/ b = Not a :-> b
a <=> b = (a :-> b) /\ b :-> a

a @+ b = Function "+" (Pair a b)

hypo =
    [Forall $ b1 `peq` b1
    ,Forall $ Forall $ Forall $ peq b1 b2 :-> (peq b2 b3 :-> peq b1 b3)
    ,Forall $ Forall $ peq b1 b2 :-> peq b2 b1
    ,Forall $ Forall $ Not (peq b1 b2) :-> Not (peq b2 b1)
    ,Forall $ Forall $ Forall $ peq b1 b2 :-> (QPred (UVar (UGen 0)) (Pair b1 b3) :->  QPred (UVar (UGen 0)) (Pair b2 b3))

--    ,n zero
--    ,Forall $ n b1 :-> n (s b1)
    ,Forall $ Not (peq zero (s b1))
    ,Forall $ Forall $ Not (peq b1 b2) :-> Not (peq (s b1) (s b2))
    ,Forall $ Forall $ (peq b1 b2) :-> (peq (s b1) (s b2))
    ,Forall $ (qp0 (Pair zero b1) /\ Forall (qp0(Pair b1 b2) :-> qp0 (Pair (s b1) b2))) :-> Forall (qp0 (Pair b1 b2))
    ,Forall $ (b1 @+ zero) `peq` b1
    ,Forall $ Forall $ (b1 @+ s b2) `peq` s (b1 @+ b2)
    ]


-- axiom schema
--
-- 1) A -> (B -> A)
-- 2) (A -> (B -> C)) -> ((A -> B) -> (A -> C))
-- 3) (!A -> !B) -> (B -> A)
--
-- 4) ∀xA -> A[x := t]
-- 5) ∀x(A -> B) -> (∀xA -> ∀xB)
-- 6) A -> ∀xA    (where x is not free in A)
--


help = unlines
    ["---- stack operations ----"
    ,"0 duplicate top of lemma stack"
    ,"1-9 move the specified formula to the top of the stack"
    ,"shift A-Z copy the specified formula from the theorem list to the top of the stack"
    ,"- delete top of lemma stack"
    ,"p promote the top of the lemma stack to a theorem"
    ,"---- rules of inference ----"
    ,"d (degeneralize) replace a quantifier with an unbound term"
    ,"g (generalize) universally quantify all unbound terms"
    ,"m use modus pones to apply the top of the stack to the second item in the stack"
    ,"---- utilities ----"
    ,"h show this help"
    ,"u undo last operation"
    ,"ESC quit"]


--------------------
-- proof searching
--------------------

search alist = ans where
    ans = do
        let alist' = concatMap degen alist
        mapM print alist'
        f alist' (pairs alist')
    f alist ((p :-> q,p'):rs) = do
        res <- modus_pones p q p'
        case res of
            Just x | formSize x < 40 -> check alist alist rs x
            _ -> f alist rs
    f alist (_:rs) = f alist rs
    f alist [] = return ()

    check alist [] rs x = do
        when (formSize x < 10) $
            print x
        f (x:alist) (rs ++ (x,x):zip (repeat x) alist ++ zip alist (repeat x))
    check alist (a:as) rs x = do
--        if a == x then f alist rs else check alist as rs x
        res <- modus_pones (skolem x) (Pred "F" zero) a
        case res of
            Just _ -> f alist rs
            Nothing -> check alist as rs x
    pairs (x:xs) = (x,x): rs ++ [ (y,x) | (x,y) <- rs ]  ++ pairs xs where
        rs = zip (repeat x) xs
    pairs [] = []
    degen (Forall x) = Forall x:degen (rmap 1 (TVar (UGen nt)) x)  where
        (_,ts) = freeVars x
        nt :: Int
        nt = head [ c | c <- [ 0 .. ], UGen c `notElem` ts]
    degen x = [x]
    rmap n w x = f n x where
        f n (Forall x) = Forall $ f (n + 1) x
        f n x = formMap (f n) (g n) x
        g n (Bound z) | z == n = w
        g n x = termMap (g n) x

formSize x = f 0 x where
    f n _ | n `seq` False = undefined
    f n (Forall x) = f (n + 1) x
    f n (a :-> b) = f n a + f 0 b
    f n (Not x) = f (n + 1) x
    f n _  = n + 1

skolem (FVar (UGen n)) = Pred ("S" ++ show n) zero
skolem x = formMap skolem id x
--------------------
-- pretty printing
--------------------

data TPEnv = TPEnv { tpChar :: !Char, tpParen :: !Bool }

instance Show Formula where
    show fl = show $ runReader tp TPEnv { tpChar = 'a', tpParen = False} where
        TP tp = formPretty fl


newtype TP a = TP (Reader TPEnv a)
    deriving(Functor, Applicative, Monad,MonadReader TPEnv)

termPretty :: Term -> TP Doc
termPretty (TVar (UGen t)) = return $ text $ 't':showIntAtBase 10 (numbers !!) t []
termPretty (Bound i) = do
    ch <- asks tpChar
    return $ char (chr (ord ch - i))
termPretty (Constant s) = return $ text s
termPretty (Function s (Pair a b)) | all (`elem` "+-*/") s = do
    a <- termPretty a
    b <- termPretty b
    return $ a <+> text s <+> b
termPretty (Function s ts) = do
    ts' <- mapM termPretty (unpair ts)
    return $ text s <> char '(' <> hsep (punctuate (char ',') ts') <> char ')'

needParen = local (\env -> env { tpParen = True })


unpair (Pair a b) = a:unpair b
unpair a = [a]

codes = (if hasUnicode then map fst else map snd)
    [("∀","!")
    ,("¬","~")
    ,(" ⇒ "," => ")
    ]

numbers = if hasUnicode then ['₀' .. '₉'] else  ['0' .. '9']

infixChars = "*/-+=%^&|"

formPretty :: Formula -> TP Doc
formPretty h = f h where
    f (Pred s (Pair a b)) | all (`elem` infixChars) s = do
        np <- asks tpParen
        a <- termPretty a
        b <- termPretty b
        let px = (a <+> text s <+> b)
        return $ if np then paren px else px
    f (a := b) = do
        np <- asks tpParen
        a <- termPretty a
        b <- termPretty b
        let px = (a <> text " = " <> b)
        return $ if np then paren px else px
    f (a :-> b) = do
        np <- asks tpParen
        a <- needParen $ f a
        b <- needParen $ f b
        let px = (a <> text (codes !! 2) <> b)
        return $ if np then paren px else px
    f (Not h)  = do
        h <- needParen $ f h
        return $ text (codes !! 1) <> h
    f (Pred s ts) = do
        ts <- mapM termPretty (unpair ts)
        return $ text s <> paren (hcat $ punctuate (char ',') ts)
    f (QPred (UVar (UGen t)) ts) = do
        ts <- mapM termPretty (unpair ts)
        return $ (char 'q' <> num t)  <> paren (hcat $ punctuate (char ',') ts)
    f (Forall h) = do
        c <- asks tpChar
        local (\e -> e { tpChar = succ c }) $ do
            h <- needParen (f h)
            return $ text (codes !! 0) <> char c <> h
    f (FVar (UGen ub)) = return $ text ('p':showIntAtBase 10 (numbers !!) ub [])
    paren x = char '(' <> x <> char ')'
    num ub = text (showIntAtBase 10 (numbers !!) ub [])
