module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacement
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.TautScaffold
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：simplicial replacement の係数の自然変換に関する関手性。
方針：各底の射列の始点の係数単体に自然変換を後合成する。
規約：通常の圏 Over(nerve C) への関手として束縛する。
使われ方：Kerodon §5.3.2（Tag 035U）、Remark 5.3.4.14（Tag 0376）、係数の比較から scaffold の比較への移行。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：係数の自然変換が simplicial replacement の射を誘導する。
方針：射列を保ち、始点における自然変換を係数単体へ後合成する。
規約：係数の充填性は要求しない。
使われ方：Kerodon §5.3.2（Tag 035U）、係数の比較の全空間への作用。 -/
def simplicialReplacementMap {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement G where
  app _ := ↾fun s ↦ ⟨s.1, s.2 ≫ η.app (s.1.obj 0)⟩
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, τ⟩
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    change (stdSimplex.map α.unop ≫ τ ≫ F.map (σ.map (homOfLE _))) ≫ η.app _ =
      stdSimplex.map α.unop ≫ (τ ≫ η.app _) ≫ G.map (σ.map (homOfLE _))
    simp only [Category.assoc]
    rw [η.naturality]

/-- 概要：係数の自然変換による全空間の射は底の射影を保つ。
方針：各次数で底の射列が変わらないことを計算する。
規約：係数の二つの図式は同じ通常の圏上にある。
使われ方：Kerodon §5.3.2（Tag 035U）、底を固定した比較射。 -/
lemma simplicialReplacementMap_projection {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) :
    simplicialReplacementMap η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection G =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F := rfl

/-- 概要：simplicial replacement の係数の恒等変換は全空間の恒等射になる。
方針：各次数の係数単体で恒等射の後合成を消去する。
規約：底の射列は固定される。
使われ方：Kerodon §5.3.2（Tag 035U）、関手の単位則。 -/
lemma simplicialReplacementMap_id {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    simplicialReplacementMap (𝟙 F) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, τ⟩
  refine Sigma.ext (by rfl) ?_
  exact heq_of_eq (Category.comp_id τ)

/-- 概要：simplicial replacement の係数の合成は全空間の射の合成になる。
方針：各次数で係数単体への後合成の結合律を使う。
規約：η の後に θ を合成する。
使われ方：Kerodon §5.3.2（Tag 035U）、関手の合成則。 -/
lemma simplicialReplacementMap_comp {C : Type u} [Category.{u} C]
    {F G H : C ⥤ SSet.{u}} (η : F ⟶ G) (θ : G ⟶ H) :
    simplicialReplacementMap (η ≫ θ) = simplicialReplacementMap η ≫ simplicialReplacementMap θ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, τ⟩
  refine Sigma.ext (by rfl) ?_
  exact heq_of_eq (Category.assoc τ (η.app _) (θ.app _)).symm

/-- 概要：simplicial replacement を底の nerve 上の単体集合への関手に束縛する。
方針：係数の自然変換の射影保存と恒等・合成則を使う。
規約：これは通常の圏の関手であり、∞ 余極限の存在の主張を含まない。
使われ方：Kerodon §5.3.2（Tag 035U）、scaffold の係数に関する比較の束縛。 -/
@[kerodon 035V]
def simplicialReplacementFunctor (C : Type u) [Category.{u} C] :
    (C ⥤ SSet.{u}) ⥤ Over (nerve C) where
  obj F := Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)
  map η := Over.homMk (simplicialReplacementMap η) (simplicialReplacementMap_projection η)
  map_id F := by
    apply Over.OverMorphism.ext
    exact simplicialReplacementMap_id F
  map_comp η θ := by
    apply Over.OverMorphism.ext
    exact simplicialReplacementMap_comp η θ

/-- 概要：taut scaffold は係数の自然変換と可換。
方針：各初区間の係数輸送と自然変換の自然性を使う。
規約：両側で同じ底の射列を保つ。
使われ方：Kerodon Remark 5.3.4.14（Tag 0376）、係数の比較に関する scaffold の自然性。 -/
@[kerodon 0376]
lemma tautScaffold_map {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) :
    simplicialReplacementMap η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold G = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, τ⟩
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext i
  change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val d.unop.len _) ≫
      (τ ≫ η.app (σ.obj 0)) ≫ G.map (σ.map (homOfLE _)) =
    (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val d.unop.len _) ≫
      τ ≫ F.map (σ.map (homOfLE _))) ≫ η.app (σ.obj i)
  simp only [Category.assoc]
  rw [η.naturality]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
