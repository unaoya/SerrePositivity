module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullIntervalEdges

/-!
概要：元実／絶対二胞体の同じ共有対角を固定 ν の実完全射として回収する。
方針：元の端点付き射データを同じ核・商へ等号で輸送する。
規約：元対角一単体と全 Hom 頂点を厳密回収。使われ方：共有対角の元全辺比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

private def zeroDiagonalArrowData (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} _⦋2⦌) :
    Σ X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}, X ⟶ Y :=
  ⟨s.obj ⟨ULift.up (0 : Fin 3)⟩, s.obj ⟨ULift.up (2 : Fin 3)⟩,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor s).map dgOdotMilnorNuNullDiagonalPath.{u}⟩

private def zeroDiagonalNormalize {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (t : Σ X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}, X ⟶ Y) (hs : t.1 = A) (ht : t.2.1 = B) : A ⟶ B :=
  eqToHom hs.symm ≫ t.2.2 ≫ eqToHom ht

private lemma zeroDiagonalHomVertex (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} _⦋2⦌)
    {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}}
    (hs : s.obj ⟨ULift.up (0 : Fin 3)⟩ = A) (ht : s.obj ⟨ULift.up (2 : Fin 3)⟩ = B) :
    (s.map ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up (2 : Fin 3)⟩ ≫
      eqToHom (congrArg₂ (fun X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1} => SimplicialCategory.sHom X Y)
        hs ht)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u}) =
      SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) A B
        (zeroDiagonalNormalize (zeroDiagonalArrowData s) hs ht) := by
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex s dgOdotMilnorNuNullDiagonalPath.{u}
  exact (congrArg (fun x => (eqToHom (congrArg₂
    (fun X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1} => SimplicialCategory.sHom X Y) hs ht)).app
      (Opposite.op ⦋0⦌) x) hv.symm).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHomVertex_transport hs ht (zeroDiagonalArrowData s).2.2)

private lemma zeroDiagonalCanonicalEdge (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} _⦋2⦌)
    {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}}
    (hs : s.obj ⟨ULift.up (0 : Fin 3)⟩ = A) (ht : s.obj ⟨ULift.up (2 : Fin 3)⟩ = B)
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}.δ (1 : Fin 3) s) =
      zeroDiagonalArrowData s) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1})
      (zeroDiagonalNormalize (zeroDiagonalArrowData s) hs ht)).edge =
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}.δ (1 : Fin 3) s := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowDataEquiv _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}).injective
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow
    (zeroDiagonalNormalize (zeroDiagonalArrowData s) hs ht)).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.arrowData_transport (zeroDiagonalArrowData s) hs ht).trans hd.symm)

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)

/-- 概要：元実上下二胞体の共有対角の固定 ν 完全射。
方針：元射データの両端を同じ元核・商へ輸送する。
規約：元対角を選び直さない。使われ方：実共有対角の全辺比較。 -/
def dgOdotMilnorNuNullDiagonalMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (K) (B) :=
  let s := dgOdotMilnorNuNullTriangle R d 0
  let f : s.obj ⟨ULift.up (0 : Fin 3)⟩ ⟶ s.obj ⟨ULift.up (2 : Fin 3)⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor s).map dgOdotMilnorNuNullDiagonalPath.{u}
  let i : (K : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) ⟶ s.obj ⟨ULift.up (0 : Fin 3)⟩ :=
    eqToHom (dgOdotMilnorNuNullTriangle_source R d 0).symm
  let p : s.obj ⟨ULift.up (2 : Fin 3)⟩ ⟶ (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) :=
    eqToHom (dgOdotMilnorNuNullTriangle_target R d 0)
  i ≫ f ≫ p

/-- 概要：元実共有対角の全 Hom 頂点は同じ固定 ν 完全射の頂点。
方針：元豊穣作用と同じ端点等号の頂点輸送式を使う。
規約：元 Hom 頂点の等号。使われ方：共有対角比較辺の端点。 -/
lemma dgOdotMilnorNuNullDiagonalMap_vertex :
    (dgOdotMilnorNuNullTriangleHom R d 0).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u}) =
      SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B)
        (dgOdotMilnorNuNullDiagonalMap R d) :=
  zeroDiagonalHomVertex (dgOdotMilnorNuNullTriangle R d 0)
    (dgOdotMilnorNuNullTriangle_source R d 0) (dgOdotMilnorNuNullTriangle_target R d 0)

/-- 概要：元実共有対角の完全射の辺は元両二胞体の同じ対角一単体。
方針：元端点付き射データの同値と元共有面の一致を使う。
規約：元全一単体の等号。使われ方：元実図式の厳密回収。 -/
lemma dgOdotMilnorNuNullDiagonalMap_edge (j : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuNullDiagonalMap R d)).edge =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}.δ (1 : Fin 3) (dgOdotMilnorNuNullTriangle R d j) := by
  have he := zeroDiagonalCanonicalEdge (dgOdotMilnorNuNullTriangle R d 0)
    (dgOdotMilnorNuNullTriangle_source R d 0) (dgOdotMilnorNuNullTriangle_target R d 0)
    (dgOdotMilnorNuNullTriangle_diagonal_data R d 0)
  fin_cases j
  · exact he
  · exact he.trans (dgOdotMilnorNuNullTriangle_diagonal R d)

variable (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：同じ絶対二胞体の共有対角の固定 ν 完全射。
方針：元絶対射データの両端を同じ核・商へ輸送する。
規約：元絶対対角を保持。使われ方：共有対角の絶対側の全辺比較。 -/
def dgOdotMilnorNuAbsoluteDiagonalMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (K) (B) :=
  let s := dgOdotMilnorNuAbsoluteNullTriangle R d h 0
  let f : s.obj ⟨ULift.up (0 : Fin 3)⟩ ⟶ s.obj ⟨ULift.up (2 : Fin 3)⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor s).map dgOdotMilnorNuNullDiagonalPath.{u}
  let i : (K : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) ⟶ s.obj ⟨ULift.up (0 : Fin 3)⟩ :=
    eqToHom (dgOdotMilnorNuAbsoluteTriangle_source R d h 0).symm
  let p : s.obj ⟨ULift.up (2 : Fin 3)⟩ ⟶ (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) :=
    eqToHom (dgOdotMilnorNuAbsoluteTriangle_target R d h 0)
  i ≫ f ≫ p

/-- 概要：元絶対共有対角の全 Hom 頂点は同じ固定 ν 完全射の頂点。
方針：元全 Hom 作用の端点輸送を使う。
規約：元 Hom 頂点の等号。使われ方：同じ共有対角比較辺の終点。 -/
lemma dgOdotMilnorNuAbsoluteDiagonalMap_vertex :
    (dgOdotMilnorNuAbsoluteTriangleHom R d h 0).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u}) =
      SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B)
        (dgOdotMilnorNuAbsoluteDiagonalMap R d h) :=
  zeroDiagonalHomVertex (dgOdotMilnorNuAbsoluteNullTriangle R d h 0)
    (dgOdotMilnorNuAbsoluteTriangle_source R d h 0)
    (dgOdotMilnorNuAbsoluteTriangle_target R d h 0)

/-- 概要：同じ絶対共有対角の完全射の辺は元両二胞体の同じ対角一単体。
方針：元射データの端点輸送と元共有面の一致を使う。
規約：元全一単体の等号。使われ方：元絶対図式の厳密回収。 -/
lemma dgOdotMilnorNuAbsoluteDiagonalMap_edge (j : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuAbsoluteDiagonalMap R d h)).edge =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}.δ (1 : Fin 3) (dgOdotMilnorNuAbsoluteNullTriangle R d h j) := by
  have he := zeroDiagonalCanonicalEdge (dgOdotMilnorNuAbsoluteNullTriangle R d h 0)
    (dgOdotMilnorNuAbsoluteTriangle_source R d h 0)
    (dgOdotMilnorNuAbsoluteTriangle_target R d h 0)
    (dgOdotMilnorNuAbsoluteTriangle_diagonal_data R d h 0)
  fin_cases j
  · exact he
  · exact he.trans (dgOdotMilnorNuAbsoluteTriangle_diagonal R d h)

end SerrePositivity.KST.SConstruction
