module
public import SerrePositivity.KST.SConstruction.SimplexIntervalOperators
public import SerrePositivity.KST.SConstruction.SimplexIntervalCubicalMapping
public import SerrePositivity.KST.SConstruction.NecklaceCubicalPostcomposition

/-! # 元の全単体作用素と全区間の cubical Hom 比較
概要：元の面・退化の Hom への作用を、同じ区間 bead の具体的 cube 射で回収する。
方針：元の余極限の生成射の後合成と、像区間への実可換三角形を照合する。
規約：同じ実射と元の次元移送を保持。使われ方：Serre Hom 比較の単体的自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の全単体作用素の全区間 cubical Hom への作用そのもの。 -/
def simplexIntervalCubicalMap {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (a b : Fin (m + 1)) :
    necklaceCubicalMapping (Δ[m] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) ⟶
      necklaceCubicalMapping (Δ[n] : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (θ.toOrderHom a)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (θ.toOrderHom b)) :=
  necklaceCubicalMap (stdSimplex.map θ) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)

/-- 元の区間の生成射と実単体作用素の後合成は、同じ像 necklace の生成射を回収する。 -/
lemma simplexIntervalCubicalCoreIso_map {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (a b : Fin (m + 1)) (hab : a ≤ b) :
    (simplexIntervalCubicalCoreIso.{u} a b hab).hom ≫ simplexIntervalCubicalMap θ a b =
      necklaceCubicalSet.map (simplexIntervalBeadMap.{u} θ a b hab) ≫
        (simplexIntervalCubicalCoreIso (θ.toOrderHom a) (θ.toOrderHom b)
          (θ.toOrderHom.monotone hab)).hom := by
  exact (necklaceCubicalCell_map (stdSimplex.map θ)
    (necklaceInSimplexInterval a b hab)).trans
      (simplexIntervalCubicalCoreIso_cell (θ.toOrderHom a) (θ.toOrderHom b)
        (θ.toOrderHom.monotone hab) (simplexIntervalImageNecklace θ a b hab)).symm

/-- 元の区間の数値次元を、同じ区間 bead の元の次元へ移す同型。 -/
def simplexIntervalCubeDimensionIso {m : ℕ} (a b : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (b.val - a.val - 1) ≅
      (necklaceConcreteCube.{u}).obj (necklaceBead (b.val - a.val)) :=
  @concreteCubeDimensionIso (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (b.val - a.val - 1))
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceBead.{u} (b.val - a.val)).down.dimension)
    (necklaceBead_dimension.{u} (b.val - a.val)).symm

/-- 元の全単体作用素の具体的 cube 射。端点の潰れる退化も同じ元の関手で扱う。 -/
def simplexIntervalCubeMap {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (a b : Fin (m + 1)) (hab : a ≤ b) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (b.val - a.val - 1) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk ((θ.toOrderHom b).val - (θ.toOrderHom a).val - 1) :=
  (simplexIntervalCubeDimensionIso.{u} a b).hom ≫
    necklaceConcreteCube.map (simplexIntervalBeadMap.{u} θ a b hab) ≫
      (simplexIntervalCubeDimensionIso.{u} (θ.toOrderHom a) (θ.toOrderHom b)).inv

/-- 元の全区間の cubical Hom 比較は、元の全単体作用素の実 cube 射と可換。 -/
lemma simplexIntervalCubicalMappingIso_map {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (a b : Fin (m + 1)) (hab : a ≤ b) :
    (simplexIntervalCubicalMappingIso.{u} a b hab).hom ≫ simplexIntervalCubicalMap θ a b =
      cubicalYoneda.map (simplexIntervalCubeMap.{u} θ a b hab) ≫
        (simplexIntervalCubicalMappingIso (θ.toOrderHom a) (θ.toOrderHom b)
          (θ.toOrderHom.monotone hab)).hom := by
  change (cubicalYoneda.map (simplexIntervalCubeDimensionIso.{u} a b).hom ≫
      (simplexIntervalCubicalCoreIso a b hab).hom) ≫ _ =
    cubicalYoneda.map ((simplexIntervalCubeDimensionIso.{u} a b).hom ≫
      necklaceConcreteCube.map (simplexIntervalBeadMap.{u} θ a b hab) ≫
        (simplexIntervalCubeDimensionIso.{u} (θ.toOrderHom a) (θ.toOrderHom b)).inv) ≫
      (cubicalYoneda.map
        (simplexIntervalCubeDimensionIso.{u} (θ.toOrderHom a) (θ.toOrderHom b)).hom ≫
          (simplexIntervalCubicalCoreIso (θ.toOrderHom a) (θ.toOrderHom b)
            (θ.toOrderHom.monotone hab)).hom)
  have h := simplexIntervalCubicalCoreIso_map.{u} θ a b hab
  have ht := (cubicalYoneda.mapIso
    (simplexIntervalCubeDimensionIso.{u} (θ.toOrderHom a) (θ.toOrderHom b))).inv_hom_id
  have hr :
      cubicalYoneda.map ((simplexIntervalCubeDimensionIso.{u} a b).hom ≫
        necklaceConcreteCube.map (simplexIntervalBeadMap.{u} θ a b hab) ≫
          (simplexIntervalCubeDimensionIso.{u} (θ.toOrderHom a) (θ.toOrderHom b)).inv) ≫
        cubicalYoneda.map
          (simplexIntervalCubeDimensionIso.{u} (θ.toOrderHom a) (θ.toOrderHom b)).hom =
      cubicalYoneda.map (simplexIntervalCubeDimensionIso.{u} a b).hom ≫
        necklaceCubicalSet.map (simplexIntervalBeadMap.{u} θ a b hab) := by
    exact (cubicalYoneda.map_comp_assoc
      (simplexIntervalCubeDimensionIso.{u} a b).hom
      (necklaceConcreteCube.map (simplexIntervalBeadMap.{u} θ a b hab) ≫
        (simplexIntervalCubeDimensionIso.{u} (θ.toOrderHom a) (θ.toOrderHom b)).inv)
      (cubicalYoneda.map
        (simplexIntervalCubeDimensionIso.{u} (θ.toOrderHom a) (θ.toOrderHom b)).hom)).trans
      (congrArg (fun f => cubicalYoneda.map
        (simplexIntervalCubeDimensionIso.{u} a b).hom ≫ f)
        ((cubicalYoneda.map_comp_assoc
          (necklaceConcreteCube.map (simplexIntervalBeadMap.{u} θ a b hab))
          (simplexIntervalCubeDimensionIso.{u} (θ.toOrderHom a) (θ.toOrderHom b)).inv
          (cubicalYoneda.map
            (simplexIntervalCubeDimensionIso.{u} (θ.toOrderHom a) (θ.toOrderHom b)).hom)).trans
          ((congrArg (fun f => cubicalYoneda.map
            (necklaceConcreteCube.map (simplexIntervalBeadMap.{u} θ a b hab)) ≫ f) ht).trans
              (Category.comp_id _))))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => cubicalYoneda.map
      (simplexIntervalCubeDimensionIso.{u} a b).hom ≫ f) h).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫ (simplexIntervalCubicalCoreIso
            (θ.toOrderHom a) (θ.toOrderHom b) (θ.toOrderHom.monotone hab)).hom)
            hr.symm).trans (Category.assoc _ _ _))))

end SerrePositivity.KST.SConstruction
