(*
infixl 9 :@
data Exp a = V a | Exp a :@ Exp a | Lam (Scope () Exp a)
  deriving (Functor,Foldable,Traversable)

-- Scope is a monad transformer
newtype Scope b f a =
  Scope (f (Var b (f a)))

Var b a ≅ a + b

-- Exp a ≅ a + (Exp a * Exp a) + Exp (1 + Exp a)

(>>>=) :: Monad f => t f a => (a -> f c) -> t f c
m >>>= f = m >>= (lift . f)

(>>=) :: Exp a -> Scope (Exp a) -> Scope
(>>>=) ::

*)

module type Recursive = sig
  type t
  type 'a base
  val base_fmap : ('a -> 'b) -> ('a base -> 'b base)
  val project : t -> t base
end

module type TyCon = sig
  type 'a t
end

module Fix0 (T : TyCon)
: sig
  type t
  val roll : t -> t T.t
  val unroll : t T.t -> t
end
= struct
  type t = Mu of t T.t
  let unroll x = Mu x
  let roll (Mu x) = x
end

(*
  f : * -> *                |-  fix0 f   ~ f (fix0 f)
  f : (* -> *) -> (* -> *)  |-  fix1 f a ~ f (fix0 f) a
 *)

module Fix1
(F : functor (T : TyCon) -> TyCon)
: sig
  module rec A : sig
    type 'a t = 'a F(A).t
  end
end
= struct
  module rec A : sig
    type 'a t = 'a F(A).t
  end = struct
    type 'a t = 'a F(A).t
  end
end

(* Fix1(F).A.t = f; f = F(M).t *)

type ('b, 'a) var =
  | B of 'b
  | F of 'a

(* new version 2023-10 *)

module type FArg = sig
  type    var
  type    self
  type 'a binder
end

module type ALG = functor (F : FArg) -> sig type t end

module BinderFix (Alg : ALG) : sig
  type 'a t

  module View (A : sig type t end) : sig
    type var = A.t
    module Arg : FArg
      with type    var    = var
      and  type    self   = var t
      and  type 'a binder = ('a, var) result t
    val roll   : Alg(Arg).t -> var t
    val unroll : var t -> Alg(Arg).t
  end
end = struct
  module rec T : sig type 'a t = Alg(Arg).t end = struct type 'a t = Alg(Arg).t end
  and Arg : sig
    type    var
    type    self   = var T.t
    type 'a binder = ('a, var) result T.t (* TODO: improve *)
  end = struct
    type    var
    type    self   = var T.t
    type 'a binder = ('a, var) result T.t
  end

  type 'a t = 'a T.t

  module View (A : sig type t end) = struct
    type var = A.t
    module Arg = struct
      type    var    = A.t
      type    self   = var t
      type 'a binder = ('a, var) result t
    end
    let roll = Obj.magic
    let unroll = Obj.magic
  end
end

module ExprF = functor (F : FArg) -> struct
  open F
  type t =
    | V   of var
    | App of self * self
    | Lam of unit binder
end
module Expr = BinderFix(ExprF)
type 'a expr = 'a Expr.t

let var   (type a) : a -> a expr =
  let open (Expr.View (struct type t = a end)) in
  fun v -> roll (V v)

let apply (type a) : a expr -> a expr -> a expr =
  let open (Expr.View (struct type t = a end)) in
  fun e1 e2 ->
    roll (App (e1, e2))

let lam   (type a) : (unit, a) result expr -> a expr =
  let open (Expr.View (struct type t = a end)) in
  fun e -> roll (Lam e)

type closed = |
let absurd : closed -> 'a = function _ -> .

let show : closed expr -> string =
  let rec go : 'a. ('a -> int) -> 'a expr -> string = fun (type a) debruijn e ->
    let open (Expr.View (struct type t = a end)) in
    match unroll e with
    | V v          -> "v" ^ string_of_int (debruijn v)
    | App (e1, e2) -> "(" ^ go debruijn e1 ^ " " ^ go debruijn e2 ^ ")"
    | Lam e        -> "λ" ^ go (function Ok () -> 0
                                       | Error v -> 1 + debruijn v) e
  in go absurd
