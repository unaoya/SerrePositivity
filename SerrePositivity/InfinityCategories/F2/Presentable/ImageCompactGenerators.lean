module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPosetImageCompact
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallFamilyGeneratorTransport
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallGeneratorPresentation
public import SerrePositivity.InfinityCategories.F2.Presentable.CompactGenerators
public import SerrePositivity.InfinityCategories.F2.Presentable.ObjectCompactCardinals

/-!
概要：像も compact な小さい生成圏を濃度変更で構成し、全 compact 対象への像の保存を得る。
方針：小さい poset 部分余極限の族を全部分模型へ移し、任意の compact 対象の retract 表示を使う。
規約：関手の compact 保存は結論とし、生成族の像の共通濃度だけを入力にする。
使われ方：引き戻しの両成分の表示と標的像を同じ濃度で調整する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：小さい全部分模型の元の包含の値は指定族の値そのもの。
方針：縮小同型で元の全部分複体へ戻し、頂点の所属条件を取り出す。
規約：同型ではなく元の頂点の等式。
使われ方：生成族の像の compact 性を全部分包含へ移す。 -/
lemma smallFullModelInclusion_vertex_eq_family
    {C : SSet.{u + 1}} (hC : Ind.HasSmallFixedVertexMaps C)
    {T : Type u} (v : T → C _⦋0⦌) (a : (smallFullModel hC v) _⦋0⦌) :
    ∃ t, (smallFullModelInclusion hC v).app _ (ULift.up a) = v t := by
  obtain ⟨t, ht⟩ := fullSubcomplexOnVertices_vertex
    ((smallFullModelIso hC v).hom.app _ (ULift.up a))
  exact ⟨t, ht.symm⟩

/-- 概要：小さい濃度変更生成圏を構成し、元の関手が全 μ-compact 対象を μ-compact に送ると示す。
方針：生成族の小さい部分余極限とその像を同時に compact にし、retract へ閉じる。
規約：元の関手には κ-filtered 保存だけを要求する。
使われ方：引き戻しの表示を標的像も compact な濃度へ揃える。 -/
lemma exists_imageCompactGenerating_of_cardinalChangeBound
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ) {A : SSet.{u}} [Quasicategory A]
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : Ind.HasSmallKappaFilteredColimits κ C) (hX : Ind.HasSmallFixedVertexMaps C)
    (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C) (hi : IsKappaCompactGenerating κ i)
    (G : C ⟶ D) (hG : IsKappaAccessibleFunctor κ G)
    (himage : ∀ a : A _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ (G.app _ (i.app _ (ULift.up a)))) :
    ∃ (A' : SSet.{u}) (hA' : Quasicategory A'),
      letI := hA'
      ∃ j : (SSet.uliftFunctor.{u + 1, u}).obj A' ⟶ C,
      IsKappaCompactGenerating μ j ∧
      ∀ x : C _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ x →
        Compact.IsKappaCompact.{u, u + 1} μ (G.app _ x) := by
  let v : SmallPosetDiagramCode κ μ A → C _⦋0⦌ := fun q ↦ q.vertex hC i
  have hg : IsKappaCompactGenerating μ (smallFullModelInclusion hX v) := by
    apply smallFullModelInclusion_isKappaCompactGenerating hX v
    · exact fun q ↦ q.vertex_isMuCompact h hC i hi.compact
    · exact fun x ↦ hi.exists_smallFamilyPresentation h hC x
  have himage' (a : (smallFullModel hX v) _⦋0⦌) :
      Compact.IsKappaCompact.{u, u + 1} μ
        (G.app _ ((smallFullModelInclusion hX v).app _ (ULift.up a))) := by
    obtain ⟨q, hq⟩ := smallFullModelInclusion_vertex_eq_family hX v a
    rw [hq]
    exact q.image_vertex_isMuCompact h hC i G hG himage
  refine ⟨smallFullModel hX v, inferInstance, smallFullModelInclusion hX v, hg, ?_⟩
  intro x hx
  obtain ⟨a, ha⟩ := hg.retract_generator hx
  exact Compact.IsKappaCompact.of_retract (ha.map G) (himage' a)

/-- 概要：accessible な標的への関手に、全 compact 対象の像を保つ共通の大きい濃度を与える。
方針：元の小さい生成族の像の濃度を揃え、部分余極限と retract の構成を使う。
規約：始域の固定頂点写像の小ささを明示する。標的の compact 保存は仮定しない。
使われ方：strict な Ind 模型上で引き戻しの二つの表示を同じ濃度へ調整する。 -/
lemma exists_compactPreservingCardinal_of_smallFixedVertexMaps
    {κ : Cardinal.{u}} {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : IsKappaAccessible κ C) (hX : Ind.HasSmallFixedVertexMaps C)
    (hD : IsAccessible D) (G : C ⟶ D) (hG : IsKappaAccessibleFunctor κ G)
    (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧ IsCardinalChangeBound κ μ ∧
      IsKappaAccessible μ C ∧
      ∀ x : C _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ x →
        Compact.IsKappaCompact.{u, u + 1} μ (G.app _ x) := by
  have : Fact κ.IsRegular := ⟨hC.1⟩
  obtain ⟨A, hA, i, hi⟩ := hC.2.2
  have := hA
  obtain ⟨ρ, _, hσρ, himage⟩ := hD.exists_common_compactCardinal
    (fun a : A _⦋0⦌ ↦ G.app _ (i.app _ (ULift.up a))) σ
  obtain ⟨μ, hμ, hρμ, hb⟩ := exists_regular_cardinalChangeBound κ ρ
  have : Fact μ.IsRegular := ⟨hμ⟩
  obtain ⟨A', hA', j, hj, hg⟩ := exists_imageCompactGenerating_of_cardinalChangeBound
    hb hC.2.1 hX i hi G hG (fun a ↦ (himage a).of_le hρμ.le)
  exact ⟨μ, hμ, hσρ.trans hρμ, hb, hC.of_cardinalChangeBound hb, hg⟩

end SerrePositivity.InfinityCategories.F2.Presentable
