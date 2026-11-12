module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CoreIsofibration

/-!
概要：QCat の実際の豊穣 Hom の後合成と、関手空間の core の後合成の一致。
方針：core の包含で比較し、豊穣単位・合成を内部 Hom の閉構造へ戻す。
規約：対象の一致だけでなく、元の指定関手による全次数の Hom 上の射を同定する。
使われ方：Cat_∞ の錐の全ての豊穣 Hom の極限性と fibration 性の検証。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：QCat の射の豊穣単位からの表示を含めると元の関手の curry になる。
方針：単位からの射を零単体で評価し、core の頂点の全単射を計算する。
規約：元の指定射 p を厳密に保持する。
使われ方：core の移送された豊穣構造を元の内部 Hom に戻す。 -/
lemma qCatHom_unit_ι (A B : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) (p : A ⟶ B) :
    eHomEquiv SSet p ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom A.obj).obj B.obj)).ι =
      curry' (show A.obj ⟶ B.obj from p) := by
  apply (SSet.unitHomEquiv _).injective
  change (((SSet.unitHomEquiv _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv _ (curry' (show A.obj ⟶ B.obj from p)))).val) = _
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv, Equiv.trans_apply]
  erw [Equiv.apply_symm_apply]
  rfl

/-- 概要：QCat の豊穣合成を含めると元の内部 Hom の合成になる。
方針：core の lax monoidal な移送と包含の定義を計算する。
規約：両方の入力の core の包含を積で合成する。
使われ方：豊穣 Hom 上の後合成の具体的な計算。 -/
lemma qCatHom_comp_ι (T A B : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) :
    eComp SSet T A B ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom T.obj).obj B.obj)).ι =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom T.obj).obj A.obj)).ι ⊗ₘ
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom A.obj).obj B.obj)).ι) ≫
          MonoidalClosed.comp T.obj A.obj B.obj := rfl

/-- 概要：QCat の豊穣 Hom 上の指定関手による作用は内部 Hom の後合成の core に等しい。
方針：包含の単射性、単位と合成の計算、閉構造の右単位則を使う。
規約：全ての試験対象 T と元の関手 p について厳密な等式を返す。
使われ方：coherent nerve の極限判定に実際の関手 core の計算を渡す。 -/
lemma qCatHom_postcomp (T A B : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) (p : A ⟶ B) :
    ((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}).obj (Opposite.op T)).map p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((ihom T.obj).map p) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom T.obj).obj B.obj)).ι).mp
  change ((ρ_ _).inv ≫ _ ◁ eHomEquiv SSet p ≫ eComp SSet T A B) ≫ _ = _
  rw [Category.assoc, Category.assoc, qCatHom_comp_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι]
  let T₀ := T.obj
  let A₀ := A.obj
  let B₀ := B.obj
  let p₀ : A₀ ⟶ B₀ := p
  let H : SSet.{u} := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom T₀).obj A₀) : SSet.{u})
  let I : SSet.{u} := (ihom A₀).obj B₀
  let hp₀ : (𝟙_ SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore I : SSet.{u}) := eHomEquiv SSet p
  have hunit : hp₀ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore I).ι = curry' p₀ := qCatHom_unit_ι A B p
  change (ρ_ H).inv ≫ H ◁ hp₀ ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom T₀).obj A₀)).ι ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore I).ι) ≫
      MonoidalClosed.comp T₀ A₀ B₀ =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom T₀).obj A₀)).ι ≫ (ihom T₀).map p₀
  rw [tensorHom_def']
  simp only [Category.assoc]
  rw [← whiskerLeft_comp_assoc, hunit, whisker_exchange_assoc,
    ← rightUnitor_inv_naturality_assoc, MonoidalClosed.whiskerLeft_curry'_comp,
    Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
