module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.StrictHomotopyLimits
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanPointHomNaturality
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramCoherentNerve
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
概要：Kan 複体の通常の錐とその豊穣 Hom の極限条件を台の単体集合で検証する。
方針：豊穣 Hom の共変作用を内部 Hom と同定し、右随伴による極限の保存を使う。
規約：F1 の KanObject、忘却関手、coherent な空間値図式をそのまま使う。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB）、γ3c の実際の空間の極限の検証。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：Kan 複体の豊穣 Hom 関手は忘却後の内部 Hom 関手に厳密に一致する。
方針：対象は定義、射は F1 の豊穣 whiskering と内部 Hom の作用の同定を使う。
規約：始域の Kan 複体 X は共通に固定する。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の実際の Hom 錐の極限性の検証。 -/
lemma kanObjectHomFunctor_eq (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj (Opposite.op X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⋙ ihom X.obj := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro Y Z f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObject_sHomWhiskerLeft X f

/-- 概要：台の単体集合で極限となる Kan 複体の錐は通常の Kan 複体の圏でも極限。
方針：忘却した錐の普遍射を使い、射の等式は台の等式として検査する。
規約：任意の小圏の図式についての主張。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の実際の strict 極限錐の公開。 -/
noncomputable def kanObjectCone_isLimit_of_forget {I : Type u} [SmallCategory I]
    {F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (c : Cone F) (hc : IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone c)) :
    IsLimit c where
  lift s := hc.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone s)
  fac s i := hc.fac (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone s) i
  uniq s m hm := hc.uniq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone s) m hm

/-- 概要：台の単体集合で極限となる Kan 複体の錐は全ての豊穣 Hom でも極限。
方針：豊穣 Hom 関手を内部 Hom と同定し、右随伴の極限保存を適用する。
規約：始域 X は任意の Kan 複体。Hom の極限性を追加仮定にしない。
使われ方：HTT 4.2.4.1 の γ3c の Hom 条件の検証。 -/
noncomputable def kanObjectHomCone_isLimit_of_forget {I : Type u} [SmallCategory I]
    {F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (c : Cone F) (hc : IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone c))
    (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c X) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram
  rw [kanObjectHomFunctor_eq]
  exact isLimitOfPreserves (ihom X.obj) hc

/-- 概要：台の図式の錐で頂点が Kan なら Kan 複体の図式の錐へ束縛できる。
方針：頂点の Kan 性を束縛し、台の脚と自然性をそのまま使う。
規約：錐の極限性は定義に不要。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の引き戻しと塔の実際の strict な錐の構成。 -/
def kanObjectConeOfUnderlying {I : Type u} [SmallCategory I] (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (c : Cone (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) (h : KanComplex c.pt) : Cone F where
  pt := ⟨c.pt, h⟩
  π :=
    { app := fun i ↦ c.π.app i
      naturality := by
        intro i j f
        change 𝟙 c.pt ≫ c.π.app j = c.π.app i ≫ (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map f
        rw [Category.id_comp]
        exact (c.w f).symm }

/-- 概要：台の錐を束縛して忘却すると元の錐に一致する。
方針：頂点と脚を定義で計算する。
規約：Kan 性の証明の選択は射の値に影響しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の strict 極限の普遍性の検証。 -/
lemma kanObjectConeOfUnderlying_forget {I : Type u} [SmallCategory I]
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (c : Cone (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) (h : KanComplex c.pt) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone (kanObjectConeOfUnderlying F c h) = c := rfl

/-- 概要：束縛した極限錐を忘却しても元の台の極限性を持つ。
方針：忘却の厳密な等式で元の普遍性を移す。
規約：元の錐の頂点が Kan であることを明示する。
使われ方：HTT 4.2.4.1 の全 Hom の極限性を検証する実際の錐の入力。 -/
noncomputable def kanObjectConeOfUnderlying_forget_isLimit {I : Type u} [SmallCategory I]
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (c : Cone (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) (h : KanComplex c.pt)
    (hc : IsLimit c) : IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone (kanObjectConeOfUnderlying F c h)) := by
  rw [kanObjectConeOfUnderlying_forget]
  exact hc

/-- 概要：Kan 複体間の fibration は豊穣 Hom の後合成でも fibration となる。
方針：内部 Hom の射の作用との同定と内部 Hom による fibration 性の保存を使う。
規約：X は任意の Kan 複体で、f の台の fibration 性を要求する。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の引き戻しと塔の Hom 条件。 -/
lemma kanObjectHom_map_fibration (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (f : Y ⟶ Z)
    [Fibration (show Y.obj ⟶ Z.obj from f)] :
    Fibration (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj (Opposite.op X)).map f) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObject_sHomWhiskerLeft]
  infer_instance

/-- 概要：strict な Kan 図式の表示は F1 の既存の空間値の coherent な図式に一致する。
方針：各単体の射列の同じ豊穣関手への写像を定義で比較する。
規約：図式は元の宇宙 u、nerve は u+1 に持ち上げる。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、F2 が使う SpaceInfinity の図式との照合。 -/
lemma strictCoherentDiagram_eq_kanDiagram {I : Type u} [SmallCategory I]
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
