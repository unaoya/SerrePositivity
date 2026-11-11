module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSourceHom

/-! # Σ に値を持つ cofiber 接続射の自然性

概要：接続射は suspension の選択に依存せず、cofiber 四角形の比較に関して自然である。
方針：始点の射を suspension 図式へ持ち上げ、S3 の対象比較の自然性で Σ へ移す。
規約：三角圏の構造を仮定せず、構成済みの suspensionFunctor を使う。
使われ方：S4 の cofiber 三角形の射と三角圏の公理。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：任意の指定 suspension の頂点を S3 の同型で Σ に移せば既存の接続射になる。
方針：標準比較同型を S3 の二つの対象比較同型で書き、合成中の逆同型を消す。
規約：suspension の零頂点の選択は自由。使われ方：Σ に値を持つ接続射の選択独立性。 -/
lemma cofiberConnectingToSuspension_comp_objIso_inv {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension t ht s ≫ s.suspensionFunctorObjIso.inv =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting_eq_via_suspensionComparison t ht s
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare.comparisonIso_eq_suspensionFunctorObjIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

/-- 概要：S3 の対象比較の逆方向も始点の射の持ち上げと Σ の射への作用に関して可換。
方針：順方向の自然性の両端に逆同型を合成する。
規約：二つの始点は異なってよい。使われ方：接続射の値域を Σ へ移す。 -/
lemma SuspensionSquare.suspensionFunctorObjIso_inv_naturality {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {x y : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare y)
    (f : SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1)).toFunctor.map (s.liftSourceHom r f) ≫
      r.suspensionFunctorObjIso.inv =
        s.suspensionFunctorObjIso.inv ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).map f := by
  have h := congrArg (fun a ↦ s.suspensionFunctorObjIso.inv ≫ a ≫ r.suspensionFunctorObjIso.inv)
    (s.suspensionFunctorObjIso_naturality r f)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using h

/-- 概要：任意の cofiber 四角形間の h の射は Σ に値を持つ接続射と可換である。
方針：始点成分を suspension 図式へ持ち上げて指定頂点での接続射の自然性を使い、Σ へ移す。
規約：余分な suspension 間の射や始点での可換式は入力しない。
使われ方：cofiber 三角形の射の第三の可換式。 -/
lemma cofiberConnecting_naturality {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t d : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) (hd : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence d)
    (a : (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d.square)) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting d hd =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).map ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map a) := by
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)
  let r := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.square 0 0)
  let f := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map a
  let b := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramHoInclusion X).map (s.liftSourceHom r f)
  have hsource : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map a ≫
      eqToHom (congrArg SSet.HomotopyCategory.mk r.source_eq.symm) =
        eqToHom (congrArg SSet.HomotopyCategory.mk s.source_eq.symm) ≫
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map b := by
    dsimp only [b]
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramHoInclusion_evaluation, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare.liftSourceHom_source]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rfl
  have hn := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension_naturality t d ht hd s r a b hsource
  have he : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map b ≫ r.suspensionFunctorObjIso.inv =
      s.suspensionFunctorObjIso.inv ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).map f := by
    dsimp only [b]
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramHoInclusion_evaluation]
    exact s.suspensionFunctorObjIso_inv_naturality r f
  rw [← cofiberConnectingToSuspension_comp_objIso_inv t ht s,
    ← cofiberConnectingToSuspension_comp_objIso_inv d hd r]
  rw [← Category.assoc, hn, Category.assoc, he, ← Category.assoc]

/-- 概要：cofiber 四角形間の実際のホモトピーが与える短複体の射は接続射と可換。
方針：ホモトピーの関手辺の類に接続射の自然性を適用し、二つの角の成分を照合する。
規約：三角圏の構造は不要。使われ方：cofiber 三角形の比較の構成。 -/
lemma cofiberConnecting_naturality_of_homotopy {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t d : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) (hd : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence d)
    (H : SSet.Homotopy t.square d.square) :
    (t.hoShortComplexMapOfHomotopy d H.h H.h₀ H.h₁).τ₃ ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting d hd =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).map
        (t.hoShortComplexMapOfHomotopy d H.h H.h₀ H.h₁).τ₁ := by
  let a := SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)
  have h₀ : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map a =
      (t.hoShortComplexMapOfHomotopy d H.h H.h₀ H.h₁).τ₁ := by
    apply Arrow.mk_injective
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluationOfEndpoints_arrow H
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0)
  have h₁ : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map a =
      (t.hoShortComplexMapOfHomotopy d H.h H.h₀ H.h₁).τ₃ := by
    apply Arrow.mk_injective
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluationOfEndpoints_arrow H
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1)
  simpa only [h₀, h₁] using cofiberConnecting_naturality t d ht hd a

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
