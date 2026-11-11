module
public import SerrePositivity.KST.SConstruction.SimplexIntervalCubicalOperators
public import SerrePositivity.KST.SConstruction.SimplexIntervalReverseHom

/-! # 元の区間 cube 作用の恒等・合成保存
概要：全単体作用素の元の具体的 cube 射と cubical Hom 射は恒等と合成を保つ。
方針：元の区間 bead 射の厳密な法則と、同じ次元移送の逆律を使う。
規約：全ての面・退化を含む元の実射。使われ方：cosimplicial dg 標準単体との比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の単体作用素の合成は、同じ元の cubical Hom 作用の合成を厳密に保つ。 -/
lemma simplexIntervalCubicalMap_comp {l m n : ℕ} (θ : ⦋l⦌ ⟶ ⦋m⦌) (φ : ⦋m⦌ ⟶ ⦋n⦌)
    (a b : Fin (l + 1)) :
    simplexIntervalCubicalMap.{u} (θ ≫ φ) a b =
      simplexIntervalCubicalMap θ a b ≫
        simplexIntervalCubicalMap φ (θ.toOrderHom a) (θ.toOrderHom b) := by
  change necklaceCubicalMap ((stdSimplex.map θ) ≫ (stdSimplex.map φ)) _ _ = _
  exact necklaceCubicalMap_comp _ _ _ _

/-- 元の恒等単体作用素は、元の次元を持つ区間 cube の恒等射を誘導する。 -/
lemma simplexIntervalCubeMap_id {m : ℕ} (a b : Fin (m + 1)) (hab : a ≤ b) :
    simplexIntervalCubeMap.{u} (𝟙 ⦋m⦌) a b hab =
      𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (b.val - a.val - 1)) := by
  change (simplexIntervalCubeDimensionIso.{u} a b).hom ≫
    necklaceConcreteCube.map (simplexIntervalBeadMap.{u} (𝟙 ⦋m⦌) a b hab) ≫
      (simplexIntervalCubeDimensionIso.{u} a b).inv = _
  exact (congrArg (fun f => (simplexIntervalCubeDimensionIso.{u} a b).hom ≫
    necklaceConcreteCube.map f ≫ (simplexIntervalCubeDimensionIso.{u} a b).inv)
    (simplexIntervalBeadMap_id a b hab)).trans
      ((congrArg (fun f => (simplexIntervalCubeDimensionIso.{u} a b).hom ≫ f ≫
        (simplexIntervalCubeDimensionIso.{u} a b).inv)
        (necklaceConcreteCube.map_id _)).trans
          ((congrArg (fun f => (simplexIntervalCubeDimensionIso.{u} a b).hom ≫ f)
            (Category.id_comp _)).trans (simplexIntervalCubeDimensionIso.{u} a b).hom_inv_id))

/-- 元の全単体作用素の合成は、元の数値次元を持つ具体的区間 cube 射の合成を保つ。 -/
lemma simplexIntervalCubeMap_comp {l m n : ℕ} (θ : ⦋l⦌ ⟶ ⦋m⦌) (φ : ⦋m⦌ ⟶ ⦋n⦌)
    (a b : Fin (l + 1)) (hab : a ≤ b) :
    simplexIntervalCubeMap.{u} (θ ≫ φ) a b hab =
      simplexIntervalCubeMap.{u} θ a b hab ≫
        simplexIntervalCubeMap.{u} φ (θ.toOrderHom a) (θ.toOrderHom b)
          (θ.toOrderHom.monotone hab) := by
  have h := congrArg (fun f => (simplexIntervalCubeDimensionIso.{u} a b).hom ≫
    necklaceConcreteCube.map f ≫
      (simplexIntervalCubeDimensionIso.{u} ((θ ≫ φ).toOrderHom a)
        ((θ ≫ φ).toOrderHom b)).inv) (simplexIntervalBeadMap_comp θ φ a b hab)
  have h' := congrArg (fun f => (simplexIntervalCubeDimensionIso.{u} a b).hom ≫ f ≫
    (simplexIntervalCubeDimensionIso.{u} ((θ ≫ φ).toOrderHom a)
      ((θ ≫ φ).toOrderHom b)).inv)
    (necklaceConcreteCube.map_comp (simplexIntervalBeadMap.{u} θ a b hab)
      (simplexIntervalBeadMap.{u} φ (θ.toOrderHom a) (θ.toOrderHom b)
        (θ.toOrderHom.monotone hab)))
  have hc {P Q R S T U : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (e : P ≅ Q) (e' : R ≅ S) (e'' : T ≅ U)
      (f : Q ⟶ S) (g : S ⟶ U) :
      e.hom ≫ (f ≫ g) ≫ e''.inv =
        (e.hom ≫ f ≫ e'.inv) ≫ (e'.hom ≫ g ≫ e''.inv) := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact h.trans (h'.trans (hc (simplexIntervalCubeDimensionIso.{u} a b)
    (simplexIntervalCubeDimensionIso.{u} (θ.toOrderHom a) (θ.toOrderHom b))
    (simplexIntervalCubeDimensionIso.{u} ((θ ≫ φ).toOrderHom a)
      ((θ ≫ φ).toOrderHom b)) _ _))

/-- 元の恒等単体作用素の cubical Hom 作用は、同じ元の Hom の恒等射。 -/
lemma simplexIntervalCubicalMap_id {m : ℕ} (a b : Fin (m + 1)) :
    simplexIntervalCubicalMap.{u} (𝟙 ⦋m⦌) a b =
      𝟙 (necklaceCubicalMapping (Δ[m] : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)) := by
  by_cases hab : a ≤ b
  · apply (cancel_epi (simplexIntervalCubicalMappingIso a b hab).hom).1
    have h := simplexIntervalCubicalMappingIso_map.{u} (𝟙 ⦋m⦌) a b hab
    exact h.trans
      ((congrArg (fun f => cubicalYoneda.map f ≫
        (simplexIntervalCubicalMappingIso a b hab).hom)
        (simplexIntervalCubeMap_id a b hab)).trans
          ((congrArg (fun f => f ≫ (simplexIntervalCubicalMappingIso a b hab).hom)
            (cubicalYoneda.map_id _)).trans
              ((Category.id_comp _).trans (Category.comp_id _).symm)))
  · exact (simplexReverseCubicalMapping_isInitial a b (lt_of_not_ge hab)).hom_ext _ _


end SerrePositivity.KST.SConstruction
