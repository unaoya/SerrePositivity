module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuAbsoluteUpperFactor
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuAbsoluteLowerFactor
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
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "Src" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "Tgt" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)

private def absoluteDiagonalNormalize {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (t : Σ X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}, X ⟶ Y) (hs : t.1 = A) (ht : t.2.1 = B) : A ⟶ B :=
  eqToHom hs.symm ≫ t.2.2 ≫ eqToHom ht

private lemma absoluteDiagonalNormalize_eq {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    {t t' : Σ X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}, X ⟶ Y} (he : t = t')
    (hs : t.1 = A) (ht : t.2.1 = B) (hs' : t'.1 = A) (ht' : t'.2.1 = B) :
    absoluteDiagonalNormalize t hs ht = absoluteDiagonalNormalize t' hs' ht' := by
  subst t'
  rfl

/-- 概要：絶対提示の元上下二単体の共有対角は固定 ν の Hom 内でも同じ頂点。
方針：同じ依存射データの等号と通常射の端点輸送の頂点式を使う。
規約：指定対角の元頂点の等号。使われ方：零成分因子分解の交点の保持。 -/
lemma dgOdotMilnorNuAbsoluteTriangleHom_diagonal :
    (dgOdotMilnorNuAbsoluteTriangleHom R d h 0).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u}) =
      (dgOdotMilnorNuAbsoluteTriangleHom R d h 1).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u}) := by
  let t (j : Fin 2) : Σ X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}, X ⟶ Y :=
    ⟨(dgOdotMilnorNuAbsoluteNullTriangle R d h j).obj ⟨ULift.up (0 : Fin 3)⟩,
      (dgOdotMilnorNuAbsoluteNullTriangle R d h j).obj ⟨ULift.up (2 : Fin 3)⟩,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (dgOdotMilnorNuAbsoluteNullTriangle R d h j)).map
        dgOdotMilnorNuNullDiagonalPath.{u}⟩
  have he : t 0 = t 1 := (dgOdotMilnorNuAbsoluteTriangle_diagonal_data R d h 0).symm.trans
    ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData (dgOdotMilnorNuAbsoluteTriangle_diagonal R d h)).trans
      (dgOdotMilnorNuAbsoluteTriangle_diagonal_data R d h 1))
  have hn := absoluteDiagonalNormalize_eq he
    (dgOdotMilnorNuAbsoluteTriangle_source R d h 0) (dgOdotMilnorNuAbsoluteTriangle_target R d h 0)
    (dgOdotMilnorNuAbsoluteTriangle_source R d h 1) (dgOdotMilnorNuAbsoluteTriangle_target R d h 1)
  have hv (j : Fin 2) : (dgOdotMilnorNuAbsoluteTriangleHom R d h j).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u}) =
      SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (Src) (Tgt)
        (absoluteDiagonalNormalize (t j) (dgOdotMilnorNuAbsoluteTriangle_source R d h j)
          (dgOdotMilnorNuAbsoluteTriangle_target R d h j)) := by
    have hv₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex
      (dgOdotMilnorNuAbsoluteNullTriangle R d h j)
      dgOdotMilnorNuNullDiagonalPath.{u}
    exact (congrArg (fun x => (eqToHom (congrArg₂
      (fun X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1} => SimplicialCategory.sHom X Y)
      (dgOdotMilnorNuAbsoluteTriangle_source R d h j)
      (dgOdotMilnorNuAbsoluteTriangle_target R d h j))).app
        (Opposite.op ⦋0⦌) x) hv₀.symm).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHomVertex_transport (dgOdotMilnorNuAbsoluteTriangle_source R d h j)
          (dgOdotMilnorNuAbsoluteTriangle_target R d h j) (t j).2.2)
  exact (hv 0).trans ((congrArg
    (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (Src) (Tgt)) hn).trans (hv 1).symm)

/-- 概要：絶対提示の元上下二単体の全 Hom の同じ零成分への因子分解。
方針：構成済みの上・下の実因子分解を同じ番号に束ねる。
規約：元全高次単体を保持。使われ方：二単体付き全指定境界の入力。 -/
def dgOdotMilnorNuAbsoluteTriangleFactor : Fin 2 →
    (nerve DGOdotMilnorNuNullTrianglePath.{u} ⟶ DGOdotMilnorNuNullCoherenceSpace R d) :=
  ![dgOdotMilnorNuAbsoluteUpperFactor R d h, dgOdotMilnorNuAbsoluteLowerFactor R d h]

/-- 概要：両零成分因子分解は同じ元二単体の全 Hom 作用を回収する。
方針：元上・下の全因子分解の包含式を使う。
規約：全単体の等号。使われ方：元実面を保つ相対充填。 -/
lemma dgOdotMilnorNuAbsoluteTriangleFactor_hom (j : Fin 2) :
    dgOdotMilnorNuAbsoluteTriangleFactor R d h j ≫ dgOdotMilnorNuNullCoherenceHom R d h =
      dgOdotMilnorNuAbsoluteTriangleHom R d h j := by
  fin_cases j
  · exact dgOdotMilnorNuAbsoluteUpperFactor_hom R d h
  · exact dgOdotMilnorNuAbsoluteLowerFactor_hom R d h

/-- 概要：両全因子分解は元共有対角の頂点を厳密に共有する。
方針：終頂点全部分複体の包含の単射性と固定 ν 対角の等号を使う。
規約：比較辺を追加しない。使われ方：元全境界の貼り合わせ。 -/
lemma dgOdotMilnorNuAbsoluteTriangleFactor_diagonal :
    (dgOdotMilnorNuAbsoluteTriangleFactor R d h 0).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u}) =
      (dgOdotMilnorNuAbsoluteTriangleFactor R d h 1).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u}) := by
  apply Subtype.ext
  exact congrArg (fun x => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (Src) (Tgt) : SSet.{u + 1})).ι.app (Opposite.op ⦋0⦌) x)
      (dgOdotMilnorNuAbsoluteTriangleHom_diagonal R d h)

end SerrePositivity.KST.SConstruction
