module
public import SerrePositivity.DifferentialGraded.Functor.Components
/-!
概要：指定斉次係数から微分・単位・合成で作る有限語とその実 Hom 評価を与える。
方針：線形結合前の語を対象・次数で添字付けし、評価と dg 関手像の可換性を帰納する。
規約：語の型は係数値を保存せず、指定生成子と対象ラベルだけに依存する。
使われ方：c′ の閉射係数を含む dg 係数閉包の自由生成元の準備。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)

inductive DGGeneratedHomWord : J → J → ℤ → Type u
  | unit (x : J) : DGGeneratedHomWord x x 0
  | generator (i : I) : DGGeneratedHomWord (source i) (target i) (degree i)
  | derivative {x y : J} {n : ℤ} (a : DGGeneratedHomWord x y n) :
      DGGeneratedHomWord x y (n + 1)
  | composition {x y z : J} {p q : ℤ}
      (a : DGGeneratedHomWord x y p) (b : DGGeneratedHomWord y z q) :
      DGGeneratedHomWord x z (p + q)

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))

namespace DGGeneratedHomWord

def evaluate {x y : J} {n : ℤ} (a : DGGeneratedHomWord source target degree x y n) :
    GradedHom R (value x) (value y) n :=
  match a with
  | .unit x => (unitElement R (value x)).val
  | .generator i => coefficient i
  | .derivative a => differential R (evaluate a)
  | .composition a b => forward R (evaluate a)
      (evaluate b) rfl

variable (E : Type w) [DGCategory R E] (F : DGFunctor R D E)

lemma evaluate_map {x y : J} {n : ℤ} (a : DGGeneratedHomWord source target degree x y n) :
    (F.map (value x) (value y)).f n (evaluate source target degree R D value coefficient a) =
      evaluate source target degree R E (F.obj ∘ value)
        (fun i => (F.map (value (source i)) (value (target i))).f (degree i) (coefficient i)) a := by
  induction a with
  | unit x => exact DGFunctor.map_unitElement R F (value x)
  | generator i => rfl
  | @derivative x y n a ih =>
    change (F.map (value x) (value y)).f (n + 1)
      (differential R (evaluate source target degree R D value coefficient a)) = _
    have h := congrArg (fun k => k (evaluate source target degree R D value coefficient a))
      ((F.map (value x) (value y)).comm n (n + 1))
    change differential R ((F.map (value x) (value y)).f n
        (evaluate source target degree R D value coefficient a)) =
      (F.map (value x) (value y)).f (n + 1)
        (differential R (evaluate source target degree R D value coefficient a)) at h
    rw [← h, ih]
    rfl
  | composition a b iha ihb =>
    change (F.map _ _).f _ (forward R _ _ rfl) = _
    rw [DGFunctor.map_forward, iha, ihb]
    rfl

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
