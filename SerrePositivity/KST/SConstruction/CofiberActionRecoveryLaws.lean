module
public import SerrePositivity.KST.SConstruction.CofiberFamilyActionLaws

/-! # 商射と基点の全単体評価からの作用法則の反映
概要：元の商射と基点での全次数の作用法則から、同じ商上の厳密な作用法則を反映する。
方針：同じ商の pushout をパラメータと tensor し、二脚で検出する。
規約：降下作用や具体的な入力模型を展開しない。使われ方：一次方向の標準豊穣化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet

/-- 元の商射と基点での全次数の合成則は、商上の全パラメータ合成則を与える。 -/
lemma cofiberAction_comp_of_app {B X B' Y B'' Z P R S : SSet.{u}}
    (j : B ⟶ X) (k : B' ⟶ Y) (l : B'' ⟶ Z)
    (a : (PointedObject.cofiber j).right ⊗ P ⟶ (PointedObject.cofiber k).right)
    (b : (PointedObject.cofiber k).right ⊗ R ⟶ (PointedObject.cofiber l).right)
    (c : (PointedObject.cofiber j).right ⊗ S ⟶ (PointedObject.cofiber l).right)
    (m : P ⊗ R ⟶ S)
    (hq : ∀ n (x : X.obj n) (p : P.obj n) (q : R.obj n),
      b.app n (a.app n ((PointedObject.cofiberQuotient j).app n x, p), q) =
        c.app n ((PointedObject.cofiberQuotient j).app n x, m.app n (p, q)))
    (hb : ∀ n (t : (𝟙_ SSet.{u}).obj n) (p : P.obj n) (q : R.obj n),
      b.app n (a.app n ((PointedObject.cofiber j).hom.app n t, p), q) =
        c.app n ((PointedObject.cofiber j).hom.app n t, m.app n (p, q))) :
    (a ⊗ₘ 𝟙 R) ≫ b = (α_ (PointedObject.cofiber j).right P R).hom ≫
      (𝟙 _ ⊗ₘ m) ≫ c := by
  apply (cancel_epi (α_ (PointedObject.cofiber j).right P R).inv).mp
  apply ((IsPushout.of_hasPushout j (toUnit B)).map
    ((tensoringRight SSet).obj (P ⊗ R))).hom_ext
  · ext n z
    exact hq n z.1 z.2.1 z.2.2
  · ext n z
    exact hb n z.1 z.2.1 z.2.2

/-- 元の商射と基点での全次数の回収式は、同じ商上の通常射の回収を与える。 -/
lemma cofiberAction_hom_of_app {B X B' Y P : SSet.{u}} (j : B ⟶ X) (k : B' ⟶ Y)
    (a : (PointedObject.cofiber j).right ⊗ P ⟶ (PointedObject.cofiber k).right)
    (p : 𝟙_ SSet.{u} ⟶ P) (f : PointedObject.cofiber j ⟶ PointedObject.cofiber k)
    (hq : ∀ n (x : X.obj n) (t : (𝟙_ SSet.{u}).obj n),
      a.app n ((PointedObject.cofiberQuotient j).app n x, p.app n t) =
        f.right.app n ((PointedObject.cofiberQuotient j).app n x))
    (hb : ∀ n (t t' : (𝟙_ SSet.{u}).obj n),
      a.app n ((PointedObject.cofiber j).hom.app n t, p.app n t') =
        f.right.app n ((PointedObject.cofiber j).hom.app n t)) :
    (𝟙 (PointedObject.cofiber j).right ⊗ₘ p) ≫ a =
      (ρ_ (PointedObject.cofiber j).right).hom ≫ f.right := by
  apply ((IsPushout.of_hasPushout j (toUnit B)).map
    ((tensoringRight SSet).obj (𝟙_ SSet.{u}))).hom_ext
  · ext n z
    exact hq n z.1 z.2
  · ext n z
    exact hb n z.1 z.2

end SerrePositivity.KST.SConstruction
