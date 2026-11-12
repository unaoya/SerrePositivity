module

public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
概要：通常の圏と nerve のホモトピー圏の間の指定された射の比較。
方針：2 次元 truncation の評価写像と元の辺の類の挿入を使う。
規約：同じ宇宙の小さい圏を扱う。
使われ方：B5 の自然変換と随伴の反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison


/-- 概要：nerve のホモトピー圏の射を通常の圏で評価する。
方針：恒等な 2 次元 truncation からの Mathlib の評価関手を使う。
規約：頂点 x は nerveEquiv x へ写る。
使われ方：自然変換の復元。 -/
def nerveHomotopyEvaluation (C : Type u) [Category.{u} C] : (nerve C).HomotopyCategory ⥤ C :=
  Truncated.HomotopyCategory.descOfTruncation (𝟙 ((truncation 2).obj (nerve C)))

/-- 概要：通常の対象・射をその nerve のホモトピー圏へ写す。
方針：射の辺と合成三角形をホモトピー圏へ写す。
規約：指定された射を変更しない。
使われ方：通常の関手圏の充満忠実な埋め込み。 -/
def nerveHomotopyInclusion (C : Type u) [Category.{u} C] : C ⥤ (nerve C).HomotopyCategory where
  obj x := HomotopyCategory.mk (nerveEquiv.symm x)
  map f := HomotopyCategory.homMk (nerve.edgeMk f)
  map_id _x := by rw [nerve.edgeMk_id, HomotopyCategory.homMk_id]
  map_comp f g := by
    obtain ⟨t⟩ := (nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl
    exact (HomotopyCategory.homMk_comp_homMk t).symm

/-- 概要：通常の射の辺の類の評価はその射に等しい。
方針：truncation の評価公式と nerve の辺の全単射を使う。
規約：元の対象を固定する。
使われ方：自然変換の逆写像の計算。 -/
lemma nerveHomotopyEvaluation_map_homMk {C : Type u} [Category.{u} C] {x y : C} (f : x ⟶ y) :
    (nerveHomotopyEvaluation C).map (HomotopyCategory.homMk (nerve.edgeMk f)) = f := by
  simp only [nerveHomotopyEvaluation, HomotopyCategory.homMk,
    Truncated.HomotopyCategory.descOfTruncation_map_homMk]
  exact nerve.homEquiv_edgeMk f

/-- 概要：評価した後に nerve の辺の類へ戻すと恒等関手になる。
方針：辺の上で確認しホモトピー圏の関手の拡張性を使う。
規約：全ての射についての関手の等式。
使われ方：充満性の証明。 -/
lemma nerveHomotopyEvaluation_comp_inclusion (C : Type u) [Category.{u} C] :
    nerveHomotopyEvaluation C ⋙ nerveHomotopyInclusion C = 𝟭 (nerve C).HomotopyCategory := by
  let hx : ∀ x : (nerve C).obj (Opposite.op ⦋0⦌),
      (nerveHomotopyEvaluation C ⋙ nerveHomotopyInclusion C).obj (HomotopyCategory.mk x) =
        (𝟭 (nerve C).HomotopyCategory).obj (HomotopyCategory.mk x) := fun x ↦
    congrArg (fun y : (nerve C).obj (Opposite.op ⦋0⦌) ↦ HomotopyCategory.mk y)
      (nerveEquiv.symm_apply_apply x)
  refine Truncated.HomotopyCategory.functor_ext hx ?_
  intro x y e
  obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective x
  obtain ⟨y, rfl⟩ := nerveEquiv.symm.surjective y
  obtain ⟨f, rfl⟩ := nerve.edgeMk_surjective e
  simp only [Functor.comp_map, Functor.id_map, eqToHom_refl, Category.id_comp,
    Category.comp_id]
  change (nerveHomotopyInclusion C).map
    ((nerveHomotopyEvaluation C).map (HomotopyCategory.homMk (nerve.edgeMk f))) = _
  rw [nerveHomotopyEvaluation_map_homMk]
  rfl

/-- 概要：通常の圏からその nerve のホモトピー圏への関手は充満忠実。
方針：評価写像を逆写像とし両方向の計算を使う。
規約：具体的な逆写像を持つ FullyFaithful 構造。
使われ方：指定された自然変換の回収。 -/
def nerveHomotopyInclusion_fullyFaithful (C : Type u) [Category.{u} C] :
    (nerveHomotopyInclusion C).FullyFaithful where
  preimage f := (nerveHomotopyEvaluation C).map f
  map_preimage f := by
    have h := CategoryTheory.Functor.congr_hom (nerveHomotopyEvaluation_comp_inclusion C) f
    simpa only [Functor.comp_map, Functor.id_map, eqToHom_refl, Category.id_comp,
      Category.comp_id] using h
  preimage_map f := nerveHomotopyEvaluation_map_homMk f

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
