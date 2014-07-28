module Language.Reflection

%access public

data TTName = UN String
            -- ^ User-provided name
            | NS TTName (List String)
            -- ^ Root, namespaces
            | MN Int String
            -- ^ Machine chosen names
            | NErased
            -- ^ Name of somethng which is never used in scope
%name TTName n, n'

implicit
userSuppliedName : String -> TTName
userSuppliedName = UN

data TTUExp = UVar Int
            -- ^ universe variable
            | UVal Int
            -- ^ explicit universe variable
%name TTUExp uexp

||| Primitive constants
data Const = I Int | BI Integer | Fl Float | Ch Char | Str String
           | IType | BIType | FlType   | ChType  | StrType
           | B8 Bits8 | B16 Bits16 | B32 Bits32 | B64 Bits64
           | B8Type   | B16Type    | B32Type    | B64Type
           | PtrType | VoidType | Forgot

%name Const c, c'

abstract class ReflConst (a : Type) where
   toConst : a -> Const

instance ReflConst Int where
   toConst x = I x

instance ReflConst Integer where
   toConst = BI

instance ReflConst Float where
   toConst = Fl

instance ReflConst Char where
   toConst = Ch

instance ReflConst String where
   toConst = Str

instance ReflConst Bits8 where
   toConst = B8

instance ReflConst Bits16 where
   toConst = B16

instance ReflConst Bits32 where
   toConst = B32

instance ReflConst Bits64 where
   toConst = B64

implicit
reflectConstant: (ReflConst a) => a -> Const
reflectConstant = toConst


||| Types of named references
data NameType = Bound
              -- ^ reference which is just bound, e.g. by intro
              | Ref
              -- ^ reference to a variable
              | DCon Int Int
              -- ^ constructor with tag and number
              | TCon Int Int
              -- ^ type constructor with tag and number
%name NameType nt, nt'

||| Types annotations for bound variables in different
||| binding contexts
data Binder a = Lam a
              | Pi a
              | Let a a
              | NLet a a
              | Hole a
              | GHole a
              | Guess a a
              | PVar a
              | PVTy a
%name Binder b, b'

instance Functor Binder where
  map f (Lam x) = Lam (f x)
  map f (Pi x) = Pi (f x)
  map f (Let x y) = Let (f x) (f y)
  map f (NLet x y) = NLet (f x) (f y)
  map f (Hole x) = Hole (f x)
  map f (GHole x) = GHole (f x)
  map f (Guess x y) = Guess (f x) (f y)
  map f (PVar x) = PVar (f x)
  map f (PVTy x) = PVTy (f x)

instance Foldable Binder where
  foldr f z (Lam x) = f x z
  foldr f z (Pi x) = f x z
  foldr f z (Let x y) = f x (f y z)
  foldr f z (NLet x y) = f x (f y z)
  foldr f z (Hole x) = f x z
  foldr f z (GHole x) = f x z
  foldr f z (Guess x y) = f x (f y z)
  foldr f z (PVar x) = f x z
  foldr f z (PVTy x) = f x z

instance Traversable Binder where
  traverse f (Lam x) = [| Lam (f x) |]
  traverse f (Pi x) = [| Pi (f x) |]
  traverse f (Let x y) = [| Let (f x) (f y) |]
  traverse f (NLet x y) = [| NLet (f x) (f y) |]
  traverse f (Hole x) = [| Hole (f x) |]
  traverse f (GHole x) = [| GHole (f x) |]
  traverse f (Guess x y) = [| Guess (f x) (f y) |]
  traverse f (PVar x) = [| PVar (f x) |]
  traverse f (PVTy x) = [| PVTy (f x) |]


||| Reflection of the well typed core language
data TT = P NameType TTName TT
        -- ^ named binders
        | V Int
        -- ^ variables
        | Bind TTName (Binder TT) TT
        -- ^ type annotated named bindings
        | App TT TT
        -- ^ (named) application of a function to a value
        | TConst Const
        -- ^ constants
        | Proj TT Int
        -- ^ argument projection; runtime only
        | Erased
        -- ^ erased terms
        | Impossible
        -- ^ impossible terms
        | TType TTUExp
        -- ^ types

%name TT tm, tm'

||| Raw terms without types
data Raw = Var TTName
         | RBind TTName (Binder Raw) Raw
         | RApp Raw Raw
         | RType
         | RForce Raw
         | RConstant Const

%name Raw tm, tm'

||| Error reports are a list of report parts
data ErrorReportPart = TextPart String
                     | NamePart TTName
                     | TermPart TT
                     | SubReport (List ErrorReportPart)
%name ErrorReportPart part, p

data Tactic = Try Tactic Tactic
            -- ^ try the first tactic and resort to the second one on failure
            | GoalType String Tactic
            -- ^ only run if the goal has the right type
            | Refine TTName
            -- ^ resolve function name, find matching arguments in the
            -- context and compute the proof target
            | Seq Tactic Tactic
            -- ^ apply both tactics in sequence
            | Trivial
            -- ^ intelligently construct the proof target from the context
            | Search Int
            -- ^ build a proof by applying contructors up to a maximum depth 
            | Instance
            -- ^ resolve a type class 
            | Solve
            -- ^ infer the proof target from the context
            | Intros
            -- ^ introduce all variables into the context
            | Intro TTName
            -- ^ introduce a named variable into the context, use the
            -- first one if the given name is not found
            | ApplyTactic TT
            -- ^ invoke the reflected rep. of another tactic
            | Reflect TT
            -- ^ turn a value into its reflected representation
            | ByReflection TT
            -- ^ use a %reflection function
            | Fill Raw
            -- ^ turn a raw value back into a term
            | Exact TT
            -- ^ use the given value to conclude the proof
            | Focus TTName
            -- ^ focus a named hole
            | Rewrite TT
            -- ^ rewrite using the reflected rep. of a equality proof
            | Induction TT
            -- ^ do induction on the particular expression
            | Case TT
            -- ^ do case analysis on particular expression
            | LetTac TTName TT
            -- ^ name a reflected term
            | LetTacTy TTName TT TT
            -- ^ name a reflected term and type it
            | Compute
            -- ^ normalise the context
            | Skip
            -- ^ do nothing
            | Fail (List ErrorReportPart)
%name Tactic tac, tac'


---------------------------------------------------------


injectiveUN : (UN x = UN y) -> x = y
injectiveUN refl = refl

injectiveNS : (NS n ns = NS n' ns') -> (n = n', ns = ns')
injectiveNS refl = (refl, refl)

injectiveMN : (MN a b = MN c d) -> (a = c, b = d)
injectiveMN refl = (refl, refl)

notUNNS : Not (UN x = NS n xs)
notUNNS refl impossible

notUNMN : Not (UN x = MN y z)
notUNMN refl impossible

notUNErased : Not (UN x = NErased)
notUNErased refl impossible

notNSMN : Not (NS n xs = MN x y)
notNSMN refl impossible

notNSErased : Not (NS n xs = NErased)
notNSErased refl impossible

notMNErased : Not (MN x y = NErased)
notMNErased refl impossible

instance DecEq TTName where
  decEq (UN x) (UN y) with (decEq x y)
    decEq (UN x) (UN x) | (Yes refl) = Yes refl
    decEq (UN x) (UN y) | (No contra) = No $ contra . injectiveUN
  decEq (UN x) (NS n xs) = No notUNNS
  decEq (UN x) (MN y z) = No notUNMN
  decEq (UN x) NErased = No notUNErased
  decEq (NS n xs) (UN x) = No $ notUNNS . sym
  decEq (NS n xs) (NS n' ys) with (decEq n n', decEq xs ys)
    decEq (NS n xs) (NS n xs)  | (Yes refl, Yes refl) = Yes refl
    decEq (NS n xs) (NS n' ys) | (Yes a, No b) = No $ b . snd . injectiveNS
    decEq (NS n xs) (NS n' ys) | (No a, b) = No $ a . fst . injectiveNS
  decEq (NS n xs) (MN x y) = No notNSMN
  decEq (NS n xs) NErased = No notNSErased
  decEq (MN x y) (UN z) = No $ notUNMN . sym
  decEq (MN x y) (NS n xs) = No $ notNSMN . sym
  decEq (MN x y) (MN z w) with (decEq x z, decEq y w)
    decEq (MN x y) (MN x y) | (Yes refl, Yes refl) = Yes refl
    decEq (MN x y) (MN z w) | (Yes a, No b ) = No $ b . snd . injectiveMN
    decEq (MN x y) (MN z w) | (No a,  b)     = No $ a . fst . injectiveMN
  decEq (MN x y) NErased = No notMNErased
  decEq NErased (UN x) = No $ notUNErased . sym
  decEq NErased (NS n xs) = No $ notNSErased . sym
  decEq NErased (MN x y) = No $ notMNErased . sym
  decEq NErased NErased = Yes refl

injectiveLam : (Lam x = Lam y) -> x = y
injectiveLam refl = refl

injectivePi : (Pi x = Pi y) -> x = y
injectivePi refl = refl

injectiveLet : (Let x y = Let w z) -> (x = w, y = z)
injectiveLet refl = (refl, refl)

injectiveNLet : (NLet x y = NLet w z) -> (x = w, y = z)
injectiveNLet refl = (refl, refl)

injectiveHole : (Hole x = Hole y) -> x = y
injectiveHole refl = refl

injectiveGHole : (GHole x = GHole y) -> x = y
injectiveGHole refl = refl

injectiveGuess : (Guess x y = Guess w z) -> (x = w, y = z)
injectiveGuess refl = (refl, refl)

injectivePVar : (PVar x = PVar y) -> x = y
injectivePVar refl = refl

injectivePVTy : (PVTy x = PVTy y) -> x = y
injectivePVTy refl = refl

notLamPi : Not (Lam x = Pi y)
notLamPi refl impossible

notLamLet : Not (Lam x = Let y z)
notLamLet refl impossible

notLamNLet : Not (Lam x = NLet y z)
notLamNLet refl impossible

notLamHole : Not (Lam x = Hole y)
notLamHole refl impossible

notLamGHole : Not (Lam x = GHole y)
notLamGHole refl impossible

notLamGuess : Not (Lam x = Guess y z)
notLamGuess refl impossible

notLamPVar : Not (Lam x = PVar y)
notLamPVar refl impossible

notLamPVTy : Not (Lam x = PVTy y)
notLamPVTy refl impossible

notPiLet : Not (Pi x = Let y z)
notPiLet refl impossible

notPiNLet : Not (Pi x = NLet y z)
notPiNLet refl impossible

notPiHole : Not (Pi x = Hole y)
notPiHole refl impossible

notPiGHole : Not (Pi x = GHole y)
notPiGHole refl impossible

notPiGuess : Not (Pi x = Guess y z)
notPiGuess refl impossible

notPiPVar : Not (Pi x = PVar y)
notPiPVar refl impossible

notPiPVTy : Not (Pi x = PVTy y)
notPiPVTy refl impossible

notLetNLet : Not (Let x y = NLet w z)
notLetNLet refl impossible

notLetHole : Not (Let x y = Hole z)
notLetHole refl impossible

notLetGHole : Not (Let x y = GHole z)
notLetGHole refl impossible

notLetGuess : Not (Let x y = Guess w z)
notLetGuess refl impossible

notLetPVar : Not (Let x y = PVar z)
notLetPVar refl impossible

notLetPVTy : Not (Let x y = PVTy z)
notLetPVTy refl impossible

notNLetHole : Not (NLet x y = Hole z)
notNLetHole refl impossible

notNLetGHole : Not (NLet x y = GHole z)
notNLetGHole refl impossible

notNLetGuess : Not (NLet x y = Guess w z)
notNLetGuess refl impossible

notNLetPVar : Not (NLet x y = PVar z)
notNLetPVar refl impossible

notNLetPVTy : Not (NLet x y = PVTy z)
notNLetPVTy refl impossible

notHoleGHole : Not (Hole x = GHole y)
notHoleGHole refl impossible

notHoleGuess : Not (Hole x = Guess y z)
notHoleGuess refl impossible

notHolePVar : Not (Hole x = PVar y)
notHolePVar refl impossible

notHolePVTy : Not (Hole x = PVTy y)
notHolePVTy refl impossible

notGHoleGuess : Not (GHole x = Guess y z)
notGHoleGuess refl impossible

notGHolePVar : Not (GHole x = PVar y)
notGHolePVar refl impossible

notGHolePVTy : Not (GHole x = PVTy y)
notGHolePVTy refl impossible

notGuessPVar : Not (Guess y x = PVar z)
notGuessPVar refl impossible

notGuessPVTy : Not (Guess y x = PVTy z)
notGuessPVTy refl impossible

notPVarPVTy : Not (PVar x = PVTy y)
notPVarPVTy refl impossible

instance DecEq t => DecEq (Binder t) where
  decEq (Lam x) (Lam y) with (decEq x y)
    decEq (Lam x) (Lam x) | (Yes refl) = Yes refl
    decEq (Lam x) (Lam y) | (No contra) = No $ contra . injectiveLam
  decEq (Lam x) (Pi y) = No notLamPi
  decEq (Lam x) (Let y z) = No notLamLet
  decEq (Lam x) (NLet y z) = No notLamNLet
  decEq (Lam x) (Hole y) = No notLamHole
  decEq (Lam x) (GHole y) = No notLamGHole
  decEq (Lam x) (Guess y z) = No notLamGuess
  decEq (Lam x) (PVar y) = No notLamPVar
  decEq (Lam x) (PVTy y) = No notLamPVTy
  decEq (Pi x) (Lam y) = No $ notLamPi . sym
  decEq (Pi x) (Pi y) with (decEq x y)
    decEq (Pi x) (Pi x) | (Yes refl) = Yes refl
    decEq (Pi x) (Pi y) | (No contra) = No $ contra . injectivePi
  decEq (Pi x) (Let y z) = No notPiLet
  decEq (Pi x) (NLet y z) = No notPiNLet
  decEq (Pi x) (Hole y) = No notPiHole
  decEq (Pi x) (GHole y) = No notPiGHole
  decEq (Pi x) (Guess y z) = No notPiGuess
  decEq (Pi x) (PVar y) = No notPiPVar
  decEq (Pi x) (PVTy y) = No notPiPVTy
  decEq (Let x y) (Lam z) = No $ notLamLet . sym
  decEq (Let x y) (Pi z) = No $ notPiLet . sym
  decEq (Let x y) (Let z w) with (decEq x z, decEq y w)
    decEq (Let x y) (Let x y) | (Yes refl, Yes refl) = Yes refl
    decEq (Let x y) (Let z w) | (Yes a, No b) = No $ b . snd . injectiveLet
    decEq (Let x y) (Let z w) | (No a, b) = No $ a . fst . injectiveLet
  decEq (Let x y) (NLet z w) = No notLetNLet
  decEq (Let x y) (Hole z) = No notLetHole
  decEq (Let x y) (GHole z) = No notLetGHole
  decEq (Let x y) (Guess z w) = No notLetGuess
  decEq (Let x y) (PVar z) = No notLetPVar
  decEq (Let x y) (PVTy z) = No notLetPVTy
  decEq (NLet x y) (Lam z) = No $ notLamNLet . sym
  decEq (NLet x y) (Pi z) = No $ notPiNLet . sym
  decEq (NLet x y) (Let z w) = No $ notLetNLet . sym
  decEq (NLet x y) (NLet z w) with (decEq x z, decEq y w)
    decEq (NLet x y) (NLet x y) | (Yes refl, Yes refl) = Yes refl
    decEq (NLet x y) (NLet z w) | (Yes a, No b) = No $ b . snd . injectiveNLet
    decEq (NLet x y) (NLet z w) | (No a, b) = No $ a . fst . injectiveNLet
  decEq (NLet x y) (Hole z) = No notNLetHole
  decEq (NLet x y) (GHole z) = No notNLetGHole
  decEq (NLet x y) (Guess z w) = No notNLetGuess
  decEq (NLet x y) (PVar z) = No notNLetPVar
  decEq (NLet x y) (PVTy z) = No notNLetPVTy
  decEq (Hole x) (Lam y) = No $ notLamHole . sym
  decEq (Hole x) (Pi y) = No $ notPiHole . sym
  decEq (Hole x) (Let y z) = No $ notLetHole . sym
  decEq (Hole x) (NLet y z) = No $ notNLetHole . sym
  decEq (Hole x) (Hole y) with (decEq x y)
    decEq (Hole x) (Hole x) | (Yes refl) = Yes refl
    decEq (Hole x) (Hole y) | (No contra) = No $ contra . injectiveHole
  decEq (Hole x) (GHole y) = No notHoleGHole
  decEq (Hole x) (Guess y z) = No notHoleGuess
  decEq (Hole x) (PVar y) = No notHolePVar
  decEq (Hole x) (PVTy y) = No notHolePVTy
  decEq (GHole x) (Lam y) = No $ notLamGHole . sym
  decEq (GHole x) (Pi y) = No $ notPiGHole . sym
  decEq (GHole x) (Let y z) = No $ notLetGHole . sym
  decEq (GHole x) (NLet y z) = No $ notNLetGHole . sym
  decEq (GHole x) (Hole y) = No $ notHoleGHole . sym
  decEq (GHole x) (GHole y) with (decEq x y)
    decEq (GHole x) (GHole x) | (Yes refl) = Yes refl
    decEq (GHole x) (GHole y) | (No contra) = No $ contra . injectiveGHole
  decEq (GHole x) (Guess y z) = No $ notGHoleGuess
  decEq (GHole x) (PVar y) = No $ notGHolePVar
  decEq (GHole x) (PVTy y) = No $ notGHolePVTy
  decEq (Guess x y) (Lam z) = No $ notLamGuess . sym
  decEq (Guess x y) (Pi z) = No $ notPiGuess . sym
  decEq (Guess x y) (Let z w) = No $ notLetGuess . sym
  decEq (Guess x y) (NLet z w) = No $ notNLetGuess . sym
  decEq (Guess x y) (Hole z) = No $ notHoleGuess . sym
  decEq (Guess x y) (GHole z) = No $ notGHoleGuess . sym
  decEq (Guess x y) (Guess z w) with (decEq x z, decEq y w)
    decEq (Guess x y) (Guess x y) | (Yes refl, Yes refl) = Yes refl
    decEq (Guess x y) (Guess x w) | (Yes refl, No b) = No $ b . snd . injectiveGuess
    decEq (Guess x y) (Guess z w) | (No a, b) = No $ a . fst . injectiveGuess
  decEq (Guess x y) (PVar z) = No $ notGuessPVar
  decEq (Guess x y) (PVTy z) = No $ notGuessPVTy
  decEq (PVar x) (Lam y) = No $ notLamPVar . sym
  decEq (PVar x) (Pi y) = No $ notPiPVar . sym
  decEq (PVar x) (Let y z) = No $ notLetPVar . sym
  decEq (PVar x) (NLet y z) = No $ notNLetPVar . sym
  decEq (PVar x) (Hole y) = No $ notHolePVar . sym
  decEq (PVar x) (GHole y) = No $ notGHolePVar . sym
  decEq (PVar x) (Guess y z) = No $ notGuessPVar . sym
  decEq (PVar x) (PVar y) with (decEq x y)
    decEq (PVar x) (PVar x) | (Yes refl) = Yes refl
    decEq (PVar x) (PVar y) | (No contra) = No $ contra . injectivePVar
  decEq (PVar x) (PVTy y) = No notPVarPVTy
  decEq (PVTy x) (Lam y) = No $ notLamPVTy . sym
  decEq (PVTy x) (Pi y) = No $ notPiPVTy . sym
  decEq (PVTy x) (Let y z) = No $ notLetPVTy . sym
  decEq (PVTy x) (NLet y z) = No $ notNLetPVTy . sym
  decEq (PVTy x) (Hole y) = No $ notHolePVTy . sym
  decEq (PVTy x) (GHole y) = No $ notGHolePVTy . sym
  decEq (PVTy x) (Guess y z) = No $ notGuessPVTy . sym
  decEq (PVTy x) (PVar y) = No $ notPVarPVTy . sym
  decEq (PVTy x) (PVTy y) with (decEq x y)
    decEq (PVTy x) (PVTy x) | (Yes refl) = Yes refl
    decEq (PVTy x) (PVTy y) | (No contra) = No $ contra . injectivePVTy

notBoundRef : Not (Bound = Ref)
notBoundRef refl impossible

notBoundDCon : Not (Bound = DCon x y)
notBoundDCon refl impossible

notBoundTCon : Not (Bound = TCon x y)
notBoundTCon refl impossible

notRefDCon : Not (Ref = DCon x y)
notRefDCon refl impossible

notRefTCon : Not (Ref = TCon x y)
notRefTCon refl impossible

notDConTCon : Not (DCon x y = TCon w z)
notDConTCon refl impossible

injectiveDCon : (DCon x y = DCon w z) -> (x = w, y = z)
injectiveDCon refl = (refl, refl)

injectiveTCon : (TCon x y = TCon w z) -> (x = w, y = z)
injectiveTCon refl = (refl, refl)


instance DecEq NameType where
  decEq Bound Bound = Yes refl
  decEq Bound Ref = No notBoundRef
  decEq Bound (DCon x y) = No notBoundDCon
  decEq Bound (TCon x y) = No notBoundTCon
  decEq Ref Bound = No $ notBoundRef . sym
  decEq Ref Ref = Yes refl
  decEq Ref (DCon x y) = No notRefDCon
  decEq Ref (TCon x y) = No notRefTCon
  decEq (DCon x y) Bound = No $ notBoundDCon . sym
  decEq (DCon x y) Ref = No $ notRefDCon . sym
  decEq (DCon x y) (DCon z w) with (decEq x z, decEq y w)
    decEq (DCon x y) (DCon x y) | (Yes refl, Yes refl) = Yes refl
    decEq (DCon x y) (DCon x w) | (Yes refl, No b) = No $ b . snd . injectiveDCon
    decEq (DCon x y) (DCon z w) | (No a, b) = No $ a . fst . injectiveDCon
  decEq (DCon x y) (TCon z w) = No notDConTCon
  decEq (TCon x y) Bound = No $ notBoundTCon . sym
  decEq (TCon x y) Ref = No $ notRefTCon . sym
  decEq (TCon x y) (DCon z w) = No $ notDConTCon . sym
  decEq (TCon x y) (TCon z w) with (decEq x z, decEq y w)
    decEq (TCon x y) (TCon x y) | (Yes refl, Yes refl) = Yes refl
    decEq (TCon x y) (TCon x w) | (Yes refl, No b) = No $ b . snd . injectiveTCon
    decEq (TCon x y) (TCon z w) | (No a, b) = No $ a . fst . injectiveTCon
