module

public import SerrePositivity.KST.NonConnective.DGSwindleInputIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedZeroVertex
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations

/-!
概要：同じ代表系内の実零加群の所属証拠を明示した、厳密な零 dg 自己関手。
方針：全 Hom を零 chain map とし、同じ閉零対象の恒等射の消滅で単位を検証する。
規約：I の前三角性から実零加群の所属は推論せず、追加の幾何的入力に隔離する。
使われ方：同じ全 native Perf 作用での零化と分裂 cofiber 族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalPreadditive
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ選択代表系が実零加群を含むという、未供給の追加証拠の型。 -/
abbrev DGKappaZeroInput : Prop := I.objects (moduleZero R D)

/-- 同じ代表系内の、元の実零加群。 -/
def dgKappaZeroObject (Z : DGKappaZeroInput R D I) : DGKappaCone R D I :=
  ⟨moduleZero R D, Z⟩

/-- 同じ実零対象を全対象で返す厳密 dg 自己関手。 -/
def dgKappaZeroFunctor (Z : DGKappaZeroInput R D I) :
    DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I) where
  obj _ := dgKappaZeroObject R D I Z
  map _ _ := 0
  map_id _ := by
    rw [comp_zero]
    change 0 = eHomEquiv (Complex R) (𝟙 (moduleZero R D))
    rw [(moduleZero_isZero R D).eq_of_src (𝟙 (moduleZero R D)) 0]
    rfl
  map_comp _ _ _ := by
    simp only [comp_zero, zero_tensor, zero_comp]

/-- 同じ零 dg 自己関手は全 Hom end の閉零圏でも実際に零対象。 -/
lemma dgKappaZeroFunctor_isZero (Z : DGKappaZeroInput R D I) :
    IsZero (ForgetEnrichment.of (Complex R) (dgKappaZeroFunctor R D I Z)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply dgFunctorClosedHom_ext R (DGKappaCone R D I) (DGKappaCone R D I)
  intro X
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  change (𝟙 (moduleZero R D)) = 0
  exact (moduleZero_isZero R D).eq_of_src _ _

end SerrePositivity.KST.NonConnective
