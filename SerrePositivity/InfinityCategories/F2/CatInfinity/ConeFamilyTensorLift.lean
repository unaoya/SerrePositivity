module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeFamilyPostcomp
public import SerrePositivity.InfinityCategories.F2.CatInfinity.InternalHomTensorLift

/-!
概要：直積内の固定図式の錐族を両成分から構成する。
方針：内部 Hom の二成分を合わせ、図式の固定条件を両射影で照合する。
規約：元の直積内の図式を全次数で固定する。
使われ方：直積の錐族の比較同型と極限性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {J X Y T : SSet.{u}} (r : J ⟶ X ⊗ Y)
variable (a : T ⟶ coneFamily (r ≫ fst X Y)) (b : T ⟶ coneFamily (r ≫ snd X Y))

/-- 概要：直積の二成分の錐族から全錐の内部 Hom の族を作る。
方針：各成分を全錐へ含めて内部 Hom の直積 lift を作る。
規約：この段階では図式固定条件を忘れている。
使われ方：直積の錐族への lift の構成。 -/
def coneFamilyTensorRawLift : T ⟶ (ihom (join (Δ[0] : SSet.{u}) J)).obj (X ⊗ Y) :=
  internalHomTensorLift
    (a ≫ vertexFiberι (coneRestriction J X) (functorVertex (r ≫ fst X Y)))
    (b ≫ vertexFiberι (coneRestriction J Y) (functorVertex (r ≫ snd X Y)))

/-- 概要：構成した全錐の族の制限は元の図式。
方針：内部 Hom の直積の二射影と各成分の図式固定条件を計算する。
規約：元の射 r を厳密に保つ。
使われ方：全錐から固定図式の錐族への移行。 -/
lemma coneFamilyTensorRawLift_restriction :
    coneFamilyTensorRawLift r a b ≫ coneRestriction J (X ⊗ Y) =
      SSet.const (functorVertex r) := by
  apply internalHomTensor_hom_ext
  · change (_ ≫ (pre (joinInr (Δ[0] : SSet.{u}) J)).app (X ⊗ Y)) ≫
      (ihom J).map (fst X Y) = _
    rw [Category.assoc, ← (pre (joinInr (Δ[0] : SSet.{u}) J)).naturality (fst X Y),
      ← Category.assoc]
    change (internalHomTensorLift _ _ ≫ _) ≫ _ = _
    rw [internalHomTensorLift_fst]
    change (a ≫ vertexFiberι (coneRestriction J X) _) ≫ coneRestriction J X = _
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.const_comp]
    rfl
  · change (_ ≫ (pre (joinInr (Δ[0] : SSet.{u}) J)).app (X ⊗ Y)) ≫
      (ihom J).map (snd X Y) = _
    rw [Category.assoc, ← (pre (joinInr (Δ[0] : SSet.{u}) J)).naturality (snd X Y),
      ← Category.assoc]
    change (internalHomTensorLift _ _ ≫ _) ≫ _ = _
    rw [internalHomTensorLift_snd]
    change (b ≫ vertexFiberι (coneRestriction J Y) _) ≫ coneRestriction J Y = _
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.const_comp]
    rfl

/-- 概要：二成分の固定図式の錐族を直積内の元の錐族へ合わせる。
方針：全錐の族を図式の頂点 fiber へ持ち上げる。
規約：始域 T は任意の単体集合。
使われ方：錐族の直積表示の逆射。 -/
def coneFamilyTensorLift : T ⟶ coneFamily r :=
  vertexFiberLift (coneRestriction J (X ⊗ Y)) (functorVertex r)
    (coneFamilyTensorRawLift r a b) (coneFamilyTensorRawLift_restriction r a b)

end SerrePositivity.InfinityCategories.F2
