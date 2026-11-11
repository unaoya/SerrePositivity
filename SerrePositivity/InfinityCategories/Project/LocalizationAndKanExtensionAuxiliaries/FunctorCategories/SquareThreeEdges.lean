module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction

/-!
概要：正方形の下辺・左辺・上辺を一つの部分単体集合として扱う。
方針：三つの辺の像の和を取り、単体ごとに各辺からの像へ帰着する。
規約：右辺を含めず、三辺への包含は単射。
使われ方：B1 の正方形の変形を三辺固定で合成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：正方形の下辺・左辺・上辺の和。
方針：各辺の包含の像の和を部分単体集合として取る。
規約：横・縦の順の座標。
使われ方：固定する三辺の制限写像の始域。 -/
noncomputable def squareThreeEdges : ((Δ[1] : SSet.{u}) ⊗ Δ[1]).Subcomplex :=
  (Subcomplex.range (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ⊔
    Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1])) ⊔
      Subcomplex.range (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1])

/-- 概要：三辺の和への下辺の包含。
方針：下辺の像が和に含まれることを使う。
規約：元の下辺へ含めると同じ射。
使われ方：相対条件から下辺の固定を取り出す。 -/
noncomputable def squareThreeEdgesBottom : (Δ[1] : SSet.{u}) ⟶ squareThreeEdges :=
  Subcomplex.lift SSet.ι₀ (le_trans le_sup_left le_sup_left)

/-- 概要：三辺の和への左辺の包含。
方針：左辺の像が和に含まれることを使う。
規約：元の左辺へ含めると同じ射。
使われ方：相対条件から左辺の固定を取り出す。 -/
noncomputable def squareThreeEdgesLeft : (Δ[1] : SSet.{u}) ⟶ squareThreeEdges :=
  Subcomplex.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1]) (le_trans le_sup_right le_sup_left)

/-- 概要：三辺の和への上辺の包含。
方針：上辺の像が和に含まれることを使う。
規約：元の上辺へ含めると同じ射。
使われ方：相対条件から上辺の固定を取り出す。 -/
noncomputable def squareThreeEdgesTop : (Δ[1] : SSet.{u}) ⟶ squareThreeEdges :=
  Subcomplex.lift SSet.ι₁ le_sup_right

/-- 概要：固定する三辺は正方形の全頂点を含む。
方針：縦座標が零なら下辺、一なら上辺から持ち上げる。
規約：高次単体での全射性は主張しない。
使われ方：三辺固定の全体ホモトピーの点ごとの可逆性。 -/
lemma squareThreeEdges_vertex_surjective :
    Function.Surjective (squareThreeEdges.{u}.ι.app (Opposite.op ⦋0⦌)) := by
  rintro ⟨s, t⟩
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective t
  refine ⟨⟨(s, stdSimplex.obj₀Equiv.symm j), ?_⟩, rfl⟩
  change ((∃ e, (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]).app _ e = _) ∨
    (∃ e, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u})).app _ e = _)) ∨
      (∃ e, (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]).app _ e = _)
  fin_cases j
  · exact Or.inl (Or.inl ⟨s, rfl⟩)
  · exact Or.inr ⟨s, rfl⟩

/-- 概要：三つの辺で一致する正方形の図式は三辺の部分図式で一致する。
方針：和の各単体をいずれかの辺からの像として表す。
規約：値域に quasicategory 性は不要。
使われ方：制限の fiber の三つの頂点を認識する。 -/
lemma squareThreeEdges_restriction_eq {Z : SSet.{u}}
    (f g : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Z)
    (hb : SSet.ι₀ ≫ f = SSet.ι₀ ≫ g)
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ≫ g)
    (ht : SSet.ι₁ ≫ f = SSet.ι₁ ≫ g) :
    squareThreeEdges.ι ≫ f = squareThreeEdges.ι ≫ g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨q, hq⟩
  change f.app n q = g.app n q
  change ((∃ e, (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]).app n e = q) ∨
    (∃ e, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u})).app n e = q)) ∨
      (∃ e, (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]).app n e = q) at hq
  rcases hq with (⟨e, rfl⟩ | ⟨e, rfl⟩) | ⟨e, rfl⟩
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app hb n) e
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app hl n) e
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app ht n) e

/-- 概要：各辺を全時間で固定する円柱の射は三辺の部分図式も固定する。
方針：各単体をいずれかの辺の像へ戻し、その辺の時間方向の等式を使う。
規約：ホモトピーの端点だけでなく raw な射を比較する。
使われ方：三辺固定のホモトピーを制限の fiber 内で合成する。 -/
lemma squareThreeEdges_homotopy_restriction {Z : SSet.{u}}
    (f : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Z)
    (H : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[1] ⟶ Z)
    (hb : ((SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) ≫ H =
      fst _ (Δ[1] : SSet.{u}) ≫ SSet.ι₀ ≫ f)
    (hl : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫ H =
      fst _ (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ≫ f)
    (ht : ((SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) ≫ H =
      fst _ (Δ[1] : SSet.{u}) ≫ SSet.ι₁ ≫ f) :
    (squareThreeEdges.ι ▷ (Δ[1] : SSet.{u})) ≫ H =
      fst _ (Δ[1] : SSet.{u}) ≫ squareThreeEdges.ι ≫ f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨q, hq⟩, t⟩
  change H.app n (q, t) = f.app n q
  change ((∃ e, (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]).app n e = q) ∨
    (∃ e, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u})).app n e = q)) ∨
      (∃ e, (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]).app n e = q) at hq
  rcases hq with (⟨e, rfl⟩ | ⟨e, rfl⟩) | ⟨e, rfl⟩
  · exact congrArg (fun k : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Z ↦ k.app n (e, t)) hb
  · exact congrArg (fun k : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Z ↦ k.app n (e, t)) hl
  · exact congrArg (fun k : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Z ↦ k.app n (e, t)) ht

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
