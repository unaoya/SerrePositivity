module
public import SerrePositivity.KST.SConstruction.Cofinality.ImageComponentBasepoint
public import SerrePositivity.KST.SConstruction.Cofinality.KZeroObjectRepresentatives

/-!
概要：元の同じ S 標的のホモトピー圏の対象を wide 成分で評価する。
方針：全頂点の wide 所属と、元の三角的分母の辺表示を使う。
規約：一般の局所化関手を新しく定義せず、指定完備化射の成分値だけを構成する。
使われ方：双積と三角形の関係を離散的障害上で検査する。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元のホモトピー圏の対象を、同じ具体的 wide 模型の成分で評価する。
方針：元の対象を表す実頂点に全辺条件の所属証拠を付ける。
規約：別の完備化模型や商圏へ置き換えない。
使われ方：障害成分上の双積演算の対象表示。 -/
def completionWideObjectClass (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (a : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier) :
    SSet.π₀ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) := by
  let F := ((multiSEndofunctor r).obj ι).map f
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F.val := stableModelHom_exact F
  exact SSet.π₀.mk ⟨a.as.as, LocalizingInvariants.completionCofiberWide_vertex F.val
    (multiSEndofunctor_map_isIdempotentCompletion r ι f hf) a.as.as⟩

/-- 概要：元の対象同型は同じ wide 成分の等号を与える。
方針：ホモトピー圏の対象を実頂点で表して既存の同型検出を使う。
規約：対象の同型だけで適用し、周囲の任意の射を同一視しない。
使われ方：双積の結合・交換・単位同型の障害側への移送。 -/
lemma completionWideObjectClass_iso (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    {a b : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier} (e : a ≅ b) :
    completionWideObjectClass r ι f hf a = completionWideObjectClass r ι f hf b := by
  obtain ⟨a, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
  obtain ⟨b, rfl⟩ := Truncated.HomotopyCategory.mk_surjective b
  exact completionWideComponent_eq_of_vertexIso r ι f hf _ _ e

/-- 概要：元の三角的分母で結ばれる対象は同じ wide 成分にある。
方針：同じホモトピー圏の射を実辺で表し、cofiber 条件から wide の辺へ持ち上げる。
規約：元の本質像による分母を使用する。
使われ方：分母と双積の関係を成分集合へ降ろす。 -/
lemma completionWideObjectClass_eq_of_trW (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    {a b : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier} (g : a ⟶ b)
    (hg : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val)).trW g) :
    completionWideObjectClass r ι f hf a = completionWideObjectClass r ι f hf b := by
  let F := ((multiSEndofunctor r).obj ι).map f
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F.val := stableModelHom_exact F
  obtain ⟨a, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
  obtain ⟨b, rfl⟩ := Truncated.HomotopyCategory.mk_surjective b
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective a b g
  have hw := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_iff_trW (LocalizingInvariants.completionEssentialImage F.val)
    e).mpr (he.symm ▸ hg)
  have hP := LocalizingInvariants.stableClosure_completionEssentialImage F.val
    (multiSEndofunctor_map_isIdempotentCompletion r ι f hf).2.1
  have hw' : e.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (LocalizingInvariants.completionEssentialImage
      F.val) := hP ▸ hw
  let t : (LocalizingInvariants.completionCofiberWide F.val : SSet.{u}) _⦋1⦌ :=
    ⟨e.edge, LocalizingInvariants.completionCofiberWide_edge F.val
      (multiSEndofunctor_map_isIdempotentCompletion r ι f hf) e.edge hw'⟩
  exact SSet.π₀.sound (SSet.Edge.mk t (Subtype.ext e.src_eq) (Subtype.ext e.tgt_eq))

end SerrePositivity.KST.SConstruction.Cofinality
