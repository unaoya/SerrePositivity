module
public import SerrePositivity.KST.SConstruction.CubicalSerreChains

/-! # cubical Serre 鎖複体の元の立方体による余極限表示
概要：全ての元の立方体からの射で鎖複体の射を構成し、その等号を判定する。
方針：点ごとの左 Kan 延長の余極限の普遍性を、元の cell 射で明示する。
規約：値域は実際の鎖複体。使われ方：全 cubical sets への Serre 対角・増大の延長。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の全立方体を添字とする鎖立方体の図式。 -/
def cubicalSerreDiagram (K : CubicalSet.{u}) :
    CostructuredArrow cubicalYoneda K ⥤ Complex A :=
  CostructuredArrow.proj cubicalYoneda K ⋙ serreConcreteCubeComplexFunctor A

/-- 鎖複体は元の全立方体の余極限と実際に同型。 -/
def cubicalSerreChainsColimitIso (K : CubicalSet.{u}) :
    (cubicalSerreChains A).obj K ≅ colimit (cubicalSerreDiagram A K) :=
  cubicalYoneda.leftKanExtensionObjIsoColimit (serreConcreteCubeComplexFunctor A) K

/-- 余極限の比較は、元の各立方体からの射を厳密に回収する。 -/
lemma cubicalSerreChainsColimitIso_cell (K : CubicalSet.{u}) (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (φ : cubicalYoneda.obj c ⟶ K) :
    (cubicalSerreChainsCubeUnit A).app c ≫ (cubicalSerreChains A).map φ ≫
        (cubicalSerreChainsColimitIso A K).hom =
      colimit.ι (cubicalSerreDiagram A K) (CostructuredArrow.mk φ) :=
  cubicalYoneda.ι_leftKanExtensionObjIsoColimit_hom _ K (CostructuredArrow.mk φ)

/-- 元の全 cell への制限で cubical 鎖複体からの射の等号を判定できる。 -/
lemma cubicalSerreChains_hom_ext {K : CubicalSet.{u}} {T : Complex A}
    {f g : (cubicalSerreChains A).obj K ⟶ T}
    (h : ∀ (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)),
      cubicalSerreCell A c x ≫ f = cubicalSerreCell A c x ≫ g) : f = g := by
  apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit cubicalYoneda
    (serreConcreteCubeComplexFunctor A) K).hom_ext'
  intro c φ
  change (cubicalSerreChainsCubeUnit A).app c ≫ (cubicalSerreChains A).map φ ≫ f =
    (cubicalSerreChainsCubeUnit A).app c ≫ (cubicalSerreChains A).map φ ≫ g
  have hx := h c (uliftYonedaEquiv φ)
  simpa only [cubicalSerreCell, cubicalCell_equiv, Category.assoc] using hx

variable (K : CubicalSet.{u}) (T : Complex A)
  (s : ∀ c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube, (cubicalYoneda.obj c ⟶ K) →
    ((serreConcreteCubeComplexFunctor A).obj c ⟶ T))
  (hs : ∀ {c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : c ⟶ d) (φ : cubicalYoneda.obj d ⟶ K),
    (serreConcreteCubeComplexFunctor A).map f ≫ s d φ = s c (cubicalYoneda.map f ≫ φ))

/-- 元の立方体の全表示関係と両立する射の族の余錐。 -/
def cubicalSerreCocone : Cocone (cubicalSerreDiagram A K) where
  pt := T
  ι :=
    { app := fun j => s j.left j.hom
      naturality := fun j k f => by
        change (serreConcreteCubeComplexFunctor A).map f.left ≫ s k.left k.hom =
          s j.left j.hom ≫ 𝟙 T
        rw [Category.comp_id, hs, CostructuredArrow.w f] }

/-- 全立方体で定めた表示関係を保つ射の族を、元の cubical 鎖複体からの射へ延長する。 -/
def cubicalSerreDesc : (cubicalSerreChains A).obj K ⟶ T :=
  (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit cubicalYoneda
    (serreConcreteCubeComplexFunctor A) K).desc (cubicalSerreCocone A K T s hs)

/-- 元の立方体への制限は、指定した射そのものを回収する。 -/
lemma cubicalSerreDesc_fac (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (φ : cubicalYoneda.obj c ⟶ K) :
    (cubicalSerreChainsCubeUnit A).app c ≫ (cubicalSerreChains A).map φ ≫
      cubicalSerreDesc A K T s hs = s c φ := by
  exact (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit cubicalYoneda
    (serreConcreteCubeComplexFunctor A) K).fac (cubicalSerreCocone A K T s hs)
      (CostructuredArrow.mk φ)

end SerrePositivity.KST.SConstruction
