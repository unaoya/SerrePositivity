module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullPrismFullBoundary

/-!
概要：元 prism 全境界から同じ全五面と上下共通の対角比較面を回収する。
方針：元 pushout の両入射と同じ全側境界の三面回収を合成する。
規約：全単体の厳密等号。使われ方：元二 prism の共通対角に沿う貼り合わせ。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：時刻を先にした元全側境界も同じ元三比較側面を厳密回収する。
方針：元因子交換の自然性と元側境界の回収式を使う。
規約：元の全三側面。使われ方：元全境界の三比較面の照合。 -/
lemma dgOdotMilnorNuNullPrismTimeBoundary_face (j : Fin 2) (i : Fin 3) :
    ((Δ[1] : SSet.{u + 2}) ◁ boundary.ι i) ≫
        dgOdotMilnorNuNullPrismTimeBoundary R d h j =
      (β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫
        dgOdotMilnorNuNullPrismSideFamily R d h j i := by
  have hs : ((Δ[1] : SSet.{u + 2}) ◁ boundary.ι i) ≫
      (β_ Δ[1] (boundary 2 : SSet.{u + 2})).hom =
        (β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫ (boundary.ι i ▷ Δ[1]) := rfl
  change ((Δ[1] : SSet.{u + 2}) ◁ boundary.ι i) ≫
    (β_ Δ[1] (boundary 2 : SSet.{u + 2})).hom ≫
      dgOdotMilnorNuNullPrismSideBoundary R d h j = _
  rw [← Category.assoc, hs, Category.assoc, dgOdotMilnorNuNullPrismSideBoundary_faces]

/-- 概要：元 prism 全境界の各側面は同じ元実ホモトピーの全族。
方針：元全側境界の入射と同じ三面回収を合成する。
規約：全パラメータの等号。使われ方：内部充填後の指定側面の回収。 -/
lemma dgOdotMilnorNuNullPrismFullBoundary_face (j : Fin 2) (i : Fin 3) :
    ((Δ[1] : SSet.{u + 2}) ◁ boundary.ι i) ≫
        Subcomplex.unionProd.ι₁ (boundary 1) (boundary 2) ≫
        dgOdotMilnorNuNullPrismFullBoundary R d h j =
      (β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫
        dgOdotMilnorNuNullPrismSideFamily R d h j i := by
  rw [dgOdotMilnorNuNullPrismFullBoundary_side]
  exact dgOdotMilnorNuNullPrismTimeBoundary_face R d h j i

/-- 概要：元三側面族の面番号一は同じ元共有対角ホモトピー。
方針：元三側面族の中央成分を回収する。
規約：元ホモトピーの全射。使われ方：上下境界の共有対角の照合。 -/
lemma dgOdotMilnorNuNullPrismSideFamily_diagonal (j : Fin 2) :
    dgOdotMilnorNuNullPrismSideFamily R d h j (1 : Fin 3) =
      (dgOdotMilnorNuNullDiagonalDiagramHomotopy R d h).h := by
  let middle (f g k : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}) :
      ![f, g, k] (1 : Fin 3) = g := rfl
  exact middle _ _ _

/-- 概要：元上下二 prism 全境界の共有対角面は同じ全比較ホモトピー。
方針：同じ面番号一の回収で、元共有対角側面を両方から取る。
規約：全正方形の厳密等号。使われ方：上下二胞体を保つ全比較の接合。 -/
lemma dgOdotMilnorNuNullPrismFullBoundary_sharedDiagonal :
    ((Δ[1] : SSet.{u + 2}) ◁ boundary.ι (1 : Fin 3)) ≫
        Subcomplex.unionProd.ι₁ (boundary 1) (boundary 2) ≫
        dgOdotMilnorNuNullPrismFullBoundary R d h 0 =
      ((Δ[1] : SSet.{u + 2}) ◁ boundary.ι (1 : Fin 3)) ≫
        Subcomplex.unionProd.ι₁ (boundary 1) (boundary 2) ≫
        dgOdotMilnorNuNullPrismFullBoundary R d h 1 := by
  exact (dgOdotMilnorNuNullPrismFullBoundary_face R d h 0 1).trans
    ((congrArg (fun f => (β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫ f)
      ((dgOdotMilnorNuNullPrismSideFamily_diagonal R d h 0).trans
        (dgOdotMilnorNuNullPrismSideFamily_diagonal R d h 1).symm)).trans
          (dgOdotMilnorNuNullPrismFullBoundary_face R d h 1 1).symm)

/-- 概要：元 prism 全境界の始端は同じ元実二胞体の全単体。
方針：元端点入射と元区間境界図式の始端回収を使う。
規約：二胞体を取り替えない。使われ方：内部充填の元実端点の固定。 -/
lemma dgOdotMilnorNuNullPrismFullBoundary_start (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 (Δ[2] : SSet.{u + 2}) ≫
        Subcomplex.unionProd.ι₂ (boundary 1) (boundary 2) ≫
        dgOdotMilnorNuNullPrismFullBoundary R d h j =
      SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d j) := by
  rw [dgOdotMilnorNuNullPrismFullBoundary_ends, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero]

/-- 概要：元 prism 全境界の終端は同じ元絶対二胞体の全単体。
方針：元端点入射と元区間境界図式の終端回収を使う。
規約：二胞体を取り替えない。使われ方：内部充填の元絶対端点の固定。 -/
lemma dgOdotMilnorNuNullPrismFullBoundary_end (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 (Δ[2] : SSet.{u + 2}) ≫
        Subcomplex.unionProd.ι₂ (boundary 1) (boundary 2) ≫
        dgOdotMilnorNuNullPrismFullBoundary R d h j =
      SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h j) := by
  rw [dgOdotMilnorNuNullPrismFullBoundary_ends, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one]

end SerrePositivity.KST.SConstruction
