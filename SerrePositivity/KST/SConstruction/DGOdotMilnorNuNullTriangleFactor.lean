module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullLowerFactor
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomConstantTransport

/-!
概要：上下元二単体の全 Hom を同じ零合成空間へ同時に保持する。
方針：同じ端点輸送を持つ共有対角の射データから因子分解の交点を照合する。
規約：元二単体と全 Hom を保持。使われ方：固定 ν 実零化面の全境界充填。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "Src" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "Tgt" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)

private def nullDiagonalNormalize {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (t : Σ X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}, X ⟶ Y) (hs : t.1 = A) (ht : t.2.1 = B) : A ⟶ B :=
  eqToHom hs.symm ≫ t.2.2 ≫ eqToHom ht

private lemma nullDiagonalNormalize_eq {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    {t t' : Σ X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}, X ⟶ Y} (he : t = t')
    (hs : t.1 = A) (ht : t.2.1 = B) (hs' : t'.1 = A) (ht' : t'.2.1 = B) :
    nullDiagonalNormalize t hs ht = nullDiagonalNormalize t' hs' ht' := by
  subst t'
  rfl

/-- 概要：元上下二単体の共有対角は固定 ν の Hom 内でも同じ頂点。
方針：同じ依存射データの等号と通常射の端点輸送の頂点式を使う。
規約：指定対角の元頂点の等号。使われ方：零成分因子分解の交点の保持。 -/
lemma dgOdotMilnorNuNullTriangleHom_diagonal :
    (dgOdotMilnorNuNullTriangleHom R d 0).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u}) =
      (dgOdotMilnorNuNullTriangleHom R d 1).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u}) := by
  let t (j : Fin 2) : Σ X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}, X ⟶ Y :=
    ⟨(dgOdotMilnorNuNullTriangle R d j).obj ⟨ULift.up (0 : Fin 3)⟩,
      (dgOdotMilnorNuNullTriangle R d j).obj ⟨ULift.up (2 : Fin 3)⟩,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (dgOdotMilnorNuNullTriangle R d j)).map
        dgOdotMilnorNuNullDiagonalPath.{u}⟩
  have he : t 0 = t 1 := (dgOdotMilnorNuNullTriangle_diagonal_data R d 0).symm.trans
    ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData (dgOdotMilnorNuNullTriangle_diagonal R d)).trans
      (dgOdotMilnorNuNullTriangle_diagonal_data R d 1))
  have hn := nullDiagonalNormalize_eq he
    (dgOdotMilnorNuNullTriangle_source R d 0) (dgOdotMilnorNuNullTriangle_target R d 0)
    (dgOdotMilnorNuNullTriangle_source R d 1) (dgOdotMilnorNuNullTriangle_target R d 1)
  have hv (j : Fin 2) : (dgOdotMilnorNuNullTriangleHom R d j).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u}) =
      SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (Src) (Tgt)
        (nullDiagonalNormalize (t j) (dgOdotMilnorNuNullTriangle_source R d j)
          (dgOdotMilnorNuNullTriangle_target R d j)) := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex (dgOdotMilnorNuNullTriangle R d j)
      dgOdotMilnorNuNullDiagonalPath.{u}
    exact (congrArg (fun x => (eqToHom (congrArg₂
      (fun X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1} => SimplicialCategory.sHom X Y)
      (dgOdotMilnorNuNullTriangle_source R d j) (dgOdotMilnorNuNullTriangle_target R d j))).app
        (Opposite.op ⦋0⦌) x) h.symm).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHomVertex_transport (dgOdotMilnorNuNullTriangle_source R d j)
          (dgOdotMilnorNuNullTriangle_target R d j) (t j).2.2)
  exact (hv 0).trans ((congrArg
    (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (Src) (Tgt)) hn).trans (hv 1).symm)

/-- 概要：元上下二単体の全 Hom の同じ零成分への因子分解。
方針：構成済みの上・下の実因子分解を同じ番号に束ねる。
規約：元全高次単体を保持。使われ方：二単体付き全指定境界の入力。 -/
def dgOdotMilnorNuNullTriangleFactor : Fin 2 →
    (nerve DGOdotMilnorNuNullTrianglePath.{u} ⟶ DGOdotMilnorNuNullCoherenceSpace R d) :=
  ![dgOdotMilnorNuNullUpperFactor R d, dgOdotMilnorNuNullLowerFactor R d]

/-- 概要：両零成分因子分解は同じ元二単体の全 Hom 作用を回収する。
方針：元上・下の全因子分解の包含式を使う。
規約：全単体の等号。使われ方：元実面を保つ相対充填。 -/
lemma dgOdotMilnorNuNullTriangleFactor_hom (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) (j : Fin 2) :
    dgOdotMilnorNuNullTriangleFactor R d j ≫ dgOdotMilnorNuNullCoherenceHom R d h =
      dgOdotMilnorNuNullTriangleHom R d j := by
  fin_cases j
  · exact dgOdotMilnorNuNullUpperFactor_hom R d h
  · exact dgOdotMilnorNuNullLowerFactor_hom R d h

/-- 概要：両全因子分解は元共有対角の頂点を厳密に共有する。
方針：終頂点全部分複体の包含の単射性と固定 ν 対角の等号を使う。
規約：比較辺を追加しない。使われ方：元全境界の貼り合わせ。 -/
lemma dgOdotMilnorNuNullTriangleFactor_diagonal :
    (dgOdotMilnorNuNullTriangleFactor R d 0).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u}) =
      (dgOdotMilnorNuNullTriangleFactor R d 1).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u}) := by
  apply Subtype.ext
  exact congrArg (fun x => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (Src) (Tgt) : SSet.{u + 1})).ι.app (Opposite.op ⦋0⦌) x)
      (dgOdotMilnorNuNullTriangleHom_diagonal R d)

end SerrePositivity.KST.SConstruction
