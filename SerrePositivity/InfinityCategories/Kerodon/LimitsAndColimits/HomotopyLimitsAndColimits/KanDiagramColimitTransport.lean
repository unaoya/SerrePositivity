module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentCoconeTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNaturalTransformation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitDiagramIso

/-!
概要：成分ごとに同値な Kan 値図式の間で、頂点を保持した実際の余極限余錐を輸送する。
方針：図式の同型を可逆円柱へ延長し、両端の coslice 制限で普遍余錐を延長・制限する。
規約：余極限の存在だけでなく元の頂点の等号を保持する。
使われ方：HTT 4.2.4.1、任意の span の単射な置換から元の図式への帰還。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
noncomputable section

/-- 概要：同型な図式の間で余極限余錐を頂点を変えず輸送できる。
方針：可逆円柱の一端から普遍余錐を延長し、他端へ制限して図式を正規化する。
規約：図式の始域は任意、値域は quasicategory。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、置換した図式の余極限を元の図式上に公開する。 -/
lemma exists_colimitCocone_functorIso_sameVertex {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso p q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d ∧ d.vertex = c.vertex := by
  obtain ⟨H, h₀, h₁⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_equivalenceCylinder_extension_of_functorIso e
  let c₀ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq h₀.symm c
  have hc₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₀ := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff h₀.symm c).mp hc
  obtain ⟨C, hC, _, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCocone_extension_of_precompositionEquivalence H
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint K false)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_equivalenceCylinderEndpoint K false) c₀ hc₀
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence H
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint K true)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_equivalenceCylinderEndpoint K true)
  have hC₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (C.restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint K true)) :=
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict H
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint K true))).isInitialVertex_iff C).mp hC
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq h₁ (C.restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint K true)),
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff h₁ _).mp hC₁, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict, hv]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex h₀.symm c

/-- 概要：図式の同型に沿って選んだ頂点を保持した余極限余錐。
方針：可逆円柱による輸送の存在から実際の余錐を選ぶ。
規約：元の余錐の余極限性を明示的に入力する。
使われ方：HTT 4.2.4.1、元の span 上の実際の余極限余錐の構成。 -/
def colimitCoconeOfFunctorIso {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso p q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q :=
  Classical.choose (exists_colimitCocone_functorIso_sameVertex e c hc)

/-- 概要：図式の同型で輸送した余錐は native な余極限余錐。
方針：選択した輸送の普遍性の証明を取り出す。
規約：輸送した実際の余錐について述べる。
使われ方：元の図式での余極限性の公開。 -/
lemma colimitCoconeOfFunctorIso_isColimit {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso p q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (colimitCoconeOfFunctorIso e c hc) :=
  (Classical.choose_spec (exists_colimitCocone_functorIso_sameVertex e c hc)).1

/-- 概要：図式の同型で輸送した余極限余錐の頂点は元の頂点。
方針：可逆円柱での延長が頂点を保つことを選択から取り出す。
規約：同値類でなく頂点の厳密な等号。
使われ方：実際の homotopy 余極限対象を図式の置換から戻して保持する。 -/
lemma colimitCoconeOfFunctorIso_vertex {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso p q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    (colimitCoconeOfFunctorIso e c hc).vertex = c.vertex :=
  (Classical.choose_spec (exists_colimitCocone_functorIso_sameVertex e c hc)).2

/-- 概要：成分ごとに同値な自然変換に沿う Kan 値図式の実際の余極限余錐の輸送。
方針：自然変換の実現の関手同型を作り、可逆円柱の余錐の輸送へ渡す。
規約：全 strict 自然変換空間の Kan 性は仮定しない。
使われ方：HTT 4.2.4.1、単射な置換した span から元の span へ戻す。 -/
def kanDiagramColimitTransport {I : Type u} [SmallCategory I]
    {F G : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (η : F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (X := (F.obj i).obj) (Y := (G.obj i).obj) (η.app i))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve G) :=
  colimitCoconeOfFunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramFunctorIsoOfPointwise
    (F := ⟨F, trivial⟩) (G := ⟨G, trivial⟩) η hη) c hc

/-- 概要：成分ごとの同値で輸送した Kan 値図式の余錐は余極限。
方針：図式の同型に沿う輸送の普遍性を適用する。
規約：元の図式 G 上の native な余極限性。
使われ方：任意の span での homotopy 押し出しの存在の検証。 -/
lemma kanDiagramColimitTransport_isColimit {I : Type u} [SmallCategory I]
    {F G : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (η : F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (X := (F.obj i).obj) (Y := (G.obj i).obj) (η.app i))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (kanDiagramColimitTransport η hη c hc) :=
  colimitCoconeOfFunctorIso_isColimit _ c hc

/-- 概要：成分ごとの同値で輸送した Kan 値図式の余極限対象は元の頂点を保持する。
方針：図式の同型による輸送の頂点の式を使う。
規約：置換後の図式の余極限対象を同じ頂点で公開する。
使われ方：任意の span の homotopy 押し出し対象の厳密な保持。 -/
lemma kanDiagramColimitTransport_vertex {I : Type u} [SmallCategory I]
    {F G : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (η : F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (X := (F.obj i).obj) (Y := (G.obj i).obj) (η.app i))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    (kanDiagramColimitTransport η hη c hc).vertex = c.vertex :=
  colimitCoconeOfFunctorIso_vertex _ c hc

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
