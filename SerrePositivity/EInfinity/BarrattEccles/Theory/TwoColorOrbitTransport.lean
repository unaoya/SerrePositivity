module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorOrbitArity
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorSeparatedInput

/-!
# 標準代表の入力表現を二色係数の群へ運ぶ

HA 3.2.4.7 の自由比較で、固定 arity の標準代表の入力を、
係数比較が使う指定二色部分群の標準入力へ同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A] (X Y : Complex A)

/-- 同じ置換作用で固定された語の等式は、表現の複体の同型を与える。 -/
def binaryTensorFixedRepresentationCongr {G : Type u} [Group G]
    {r : ℕ} {w z : BinaryTensorWord r} (h : w = z) (φ : G →* Equiv.Perm (Fin r))
    (hw : ∀ g, φ g • w = w) (hz : ∀ g, φ g • z = z) :
    binaryTensorWordFixedRepresentation X Y r w φ hw ≅
      binaryTensorWordFixedRepresentation X Y r z φ hz := by
  subst z
  exact Iso.refl _

namespace BarrattEccles
variable (m n : ℕ)

/-- 群を同定すると、同じ標準代表を固定する置換は元の指定置換である。 -/
lemma twoColorCountPattern_fixed (g : TwoColorGroup.{u} m n) :
    twoColorInputPermutation m n g • binaryTensorCountPattern (m + n) ⟨m, by omega⟩ =
      binaryTensorCountPattern (m + n) ⟨m, by omega⟩ := by
  rw [binaryTensorCountPattern_add]
  exact twoColorInputPermutation_fixed m n g

/-- 標準代表の群を移しても、作用と元の微分は指定された固定入力のものになる。 -/
def twoColorOrbitRestrictionIso :
    ((Rep.resFunctor (binaryTensorPatternGroupEquiv m n).symm.toMonoidHom).mapHomologicalComplex
       (.up ℤ)).obj
        (binaryTensorOrbitInput X Y (m + n) (ULift.up ⟨m, by omega⟩)) ≅
      binaryTensorWordFixedRepresentation X Y (m + n)
        (binaryTensorCountPattern (m + n) ⟨m, by omega⟩)
        (twoColorInputPermutation m n) (twoColorCountPattern_fixed m n) :=
  Iso.refl _

/-- 実際の軌道入力を、係数比較の群上の指定標準入力へ同定する。 -/
def twoColorOrbitStandardInputIso :
    ((Rep.resFunctor (binaryTensorPatternGroupEquiv m n).symm.toMonoidHom).mapHomologicalComplex
       (.up ℤ)).obj
        (binaryTensorOrbitInput X Y (m + n) (ULift.up ⟨m, by omega⟩)) ≅
      twoColorStandardInput X Y m n :=
  twoColorOrbitRestrictionIso X Y m n ≪≫
    binaryTensorFixedRepresentationCongr X Y (binaryTensorCountPattern_add m n)
      (twoColorInputPermutation m n) (twoColorCountPattern_fixed m n)
      (twoColorInputPermutation_fixed m n)

end BarrattEccles
end SerrePositivity.EInfinity
