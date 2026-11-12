module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.DiscreteHomColimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanConeLimits
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
概要：Kan 複体の余錐の全反変豊穣 Hom の極限性を台の余極限から検証する。
方針：反対圏の豊穣 Hom を内部 Hom の反変関手と同定し、極限保存を使う。
規約：余錐の頂点が Kan であることは対象の束縛で保持する。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、𝒮 の実際の余積の Hom 条件。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed BraidedCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：Kan 複体の反対圏の豊穣 Hom 関手は反変の内部 Hom と一致する。
方針：射の作用を braiding と豊穣合成で展開し、内部 Hom の前合成の式を使う。
規約：固定対象 X に対する Hom(−,X) の共変な反対圏表示。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、余極限の Hom の極限性の検証。 -/
lemma kanObjectOppositeHomFunctor_eq (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ).obj (Opposite.op (Opposite.op X)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.op ⋙ (internalHom (C := SSet.{u})).flip.obj X.obj := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro Y Z f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (ρ_ ((ihom Y.unop.obj).obj X.obj)).inv ≫
    ((ihom Y.unop.obj).obj X.obj) ◁ curry' (C := SSet.{u}) f.unop ≫
    (β_ _ _).hom ≫ MonoidalClosed.comp Z.unop.obj Y.unop.obj X.obj = _
  rw [braiding_naturality_right_assoc, braiding_tensorUnit_right]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [curry'_whiskerRight_comp, Iso.inv_hom_id_assoc]
  rfl

/-- 概要：台の単体集合で余極限となる Kan 複体の余錐は通常の圏でも余極限。
方針：台の余極限の降下射を束縛された対象間の射として使う。
規約：添字は任意の小圏。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、実際の strict な余積の普遍性。 -/
noncomputable def kanObjectCocone_isColimit_of_forget {I : Type u} [SmallCategory I]
    {F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (c : Cocone F)
    (hc : IsColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone c)) : IsColimit c where
  desc s := hc.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone s)
  fac s i := hc.fac (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone s) i
  uniq s m hm := hc.uniq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone s) m hm

/-- 概要：台で余極限となる Kan 複体の余錐は全ての反変豊穣 Hom で極限となる。
方針：余極限を反対の極限へ移し、内部 Hom の反変変数の極限保存を使う。
規約：Hom の極限性を追加の仮定にしない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB） の豊穣余積の検証。 -/
noncomputable def kanObjectOppositeHomCone_isLimit_of_forget
    {I : Type u} [SmallCategory I] {F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (c : Cocone F)
    (hc : IsColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone c)) (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c.op X) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram
  rw [kanObjectOppositeHomFunctor_eq X.unop]
  exact isLimitOfPreserves ((internalHom (C := SSet.{u})).flip.obj X.unop.obj) hc.op

/-- 概要：離散な小圏上の台の余極限は空間の ∞ 圏の実際の余極限錐を与える。
方針：台の普遍性から全反変 Hom の極限性を証明し、豊穣余積の移送定理へ渡す。
規約：与えた Kan な頂点と元の標準図式を保持し、追加の比較同値を要求しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、𝒮 の小さい余積への界面。 -/
lemma strictNativeCocone_isColimit_of_kanDiscrete_forget
    {I : Type u} [SmallCategory I] [IsDiscrete I] {F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (c : Cocone F) (hc : IsColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictNativeCocone_isColimit_of_isDiscrete_homLimit c
    (kanObjectOppositeHomCone_isLimit_of_forget c hc)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
