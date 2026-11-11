module
public import SerrePositivity.KST.SConstruction.Cofinality.WideStageInput

/-!
概要：供給値の wide 部分複体を同じ全多次数の S 構造射で結ぶ。
方針：完全な構造射で cofiber と像同型を写し、全単体条件へ戻す。
規約：供給値の選択の自然性を新しい仮定としない。
使われ方：相対 S• の全方向の面・退化の組立。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：反復 S の全構造射は、指定射の像に cofiber が入る辺を保つ。
方針：同じ cofiber 四角形と像同型を完全な構造射で写す。
規約：構造射と元の f の厳密な自然性を使用する。
使われ方：各多次数の wide 部分複体間の実射。 -/
lemma multiS_map_cofiberImageEdge (r : ℕ)
    {ι κ : Fin r → SimplexCategoryᵒᵖ} (α : ι ⟶ κ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (a : (((multiSEndofunctor r).obj ι).obj Y).carrier _⦋1⦌)
    (ha : a ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {y | ∃ x, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
        ((((multiSEndofunctor r).obj ι).map f).val.app (Opposite.op ⦋0⦌) x) y)}) :
    (((multiSEndofunctor r).map α).app Y).val.app (Opposite.op ⦋1⦌) a ∈
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {y | ∃ x, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
        ((((multiSEndofunctor r).obj κ).map f).val.app (Opposite.op ⦋0⦌) x) y)} := by
  let gX := ((multiSEndofunctor r).map α).app X
  let gY := ((multiSEndofunctor r).map α).app Y
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor gY.val := stableModelHom_exact gY
  obtain ⟨s, z, ⟨x, ⟨e⟩⟩, ⟨ez⟩⟩ := ha
  let t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (gY.val.app (Opposite.op ⦋1⦌) a)) := {
    toZeroTriangle := (s.map gY.val).toZeroTriangle
    bottom_edge := (s.map gY.val).bottom_edge
    isPushout := (s.map gY.val).isPushout }
  refine ⟨t, gY.val.app (Opposite.op ⦋0⦌) z, ?_, ⟨ez.map gY.val⟩⟩
  refine ⟨gX.val.app (Opposite.op ⦋0⦌) x, ?_⟩
  have h := congrArg (fun q : ((multiSEndofunctor r).obj ι).obj X ⟶
      ((multiSEndofunctor r).obj κ).obj Y => q.val.app (Opposite.op ⦋0⦌) x)
    (((multiSEndofunctor r).map α).naturality f)
  exact h ▸ Nonempty.intro (e.map gY.val)

/-- 概要：wide 供給の各単体は全多次数の S 構造射で次の供給値へ入る。
方針：辺の像保存と単体の全辺条件を組み合わせる。
規約：異なる多次数の供給値の等号や選択の自然性を仮定しない。
使われ方：全多単体的 wide 図式の射の所属証明。 -/
lemma multiWideStageData_map_mem (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) {ι κ : Fin r → SimplexCategoryᵒᵖ} (α : ι ⟶ κ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (n : ℕ) (s : (((multiSEndofunctor r).obj ι).obj Y).carrier _⦋n⦌)
    (hs : s ∈ (multiWideStageData supply r ι f hf).subcomplex.obj (Opposite.op ⦋n⦌)) :
    (((multiSEndofunctor r).map α).app Y).val.app (Opposite.op ⦋n⦌) s ∈
      (multiWideStageData supply r κ f hf).subcomplex.obj (Opposite.op ⦋n⦌) := by
  apply ((multiWideStageData supply r κ f hf).simplex_spec n _).mpr
  intro θ
  have h := multiS_map_cofiberImageEdge r α f _
    (((multiWideStageData supply r ι f hf).simplex_spec n s).mp hs θ)
  exact (ConcreteCategory.congr_hom
    ((((multiSEndofunctor r).map α).app Y).val.naturality θ.op) s) ▸ h

/-- 概要：全多次数の元の S 構造射を wide 供給値へ制限する。
方針：元の単体の像に全辺条件の保存証明を添える。
規約：包含後は元の構造射を厳密に保持する。
使われ方：相対旗の多次数方向の実作用。 -/
def multiWideStageMap (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) {ι κ : Fin r → SimplexCategoryᵒᵖ} (α : ι ⟶ κ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    ((multiWideStageData supply r ι f hf).subcomplex : SSet.{u}) ⟶
      ((multiWideStageData supply r κ f hf).subcomplex : SSet.{u}) where
  app d := ↾fun s => ⟨(((multiSEndofunctor r).map α).app Y).val.app d s.val,
    multiWideStageData_map_mem supply r α f hf d.unop.len s.val s.property⟩
  naturality {d e} β := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((((multiSEndofunctor r).map α).app Y).val.naturality β) s.val

/-- 概要：供給値の wide 部分複体は全多次数の厳密な図式をなす。
方針：元の多単体的 S 関手の法則を部分型の値へ移す。
規約：供給値の選択を関手的な選択に変更しない。
使われ方：相対実現の wide 側の多単体図式。 -/
def multiWideStageDiagram (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u} where
  obj ι := (multiWideStageData supply r ι f hf).subcomplex
  map α := multiWideStageMap supply r α f hf
  map_id ι := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact congrArg (fun t : ((multiSEndofunctor r).obj ι) ⟶
      ((multiSEndofunctor r).obj ι) => (t.app Y).val.app d s.val)
      ((multiSEndofunctor r).map_id ι)
  map_comp {ι κ μ} α β := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact congrArg (fun t : ((multiSEndofunctor r).obj ι) ⟶
      ((multiSEndofunctor r).obj μ) => (t.app Y).val.app d s.val)
      ((multiSEndofunctor r).map_comp α β)

/-- 概要：wide 図式から元の全多次数の反復 S への厳密な自然包含。
方針：各多次数の部分複体包含を束ねる。
規約：対象も構造射も元の未置換反復 S を使う。
使われ方：相対旗と元の K 構成の間の自然比較。 -/
def multiWideStageInclusion (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    multiWideStageDiagram supply r f hf ⟶ multiSConstruction r Y where
  app ι := (multiWideStageData supply r ι f hf).subcomplex.ι
  naturality _ _ _ := rfl

end SerrePositivity.KST.SConstruction.Cofinality
