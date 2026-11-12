module
public import SerrePositivity.KST.SConstruction.SimplexSubsetUniformFaceBoundary
public import SerrePositivity.KST.SConstruction.SerreCubeTopCellImageDifferentialTransport

/-! # 元の native HA 成分微分の統一した全面和
概要：元の HA 成分の微分を、元の統一した面像の符号付き差の全面和として回収する。
方針：元の成分・最高生成元の次元移送、元の全面微分、元の面座標の移送を合成する。
規約：元の実 dg 関手と微分を保持。使われ方：全高次 HA 方程式の微分側と右辺の一致。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped BigOperators
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の native HA 成分の微分は、元の同じ全体 cube の統一した標準両面像の全面和。 -/
lemma cubicalLambdaNativeSimplexData_differential_uniform_faces {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (h3 : 3 ≤ I.card) :
    differential A ((cubicalLambdaNativeSimplexData A F).hom I
        (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
        (2 - (I.card : ℤ)) hI rfl rfl rfl) =
      ∑ i : Fin (I.card - 2), ((i.val : ℤ) + 1).negOnePow •
        (simplexSubsetUniformFaceTopImage A false F I hI h3 i -
          simplexSubsetUniformFaceTopImage A true F I hI h3 i) := by
  let a := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
  let b := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
  let H := homObject A D (F.obj a) (F.obj b)
  let N := I.card - 3
  let k : ℤ := 2 - (I.card : ℤ)
  have hd : I.card - 2 = N + 1 := by dsimp [N]; omega
  have hk : -((N + 1 : ℕ) : ℤ) = k := by dsimp [N, k]; omega
  have ht : -(N : ℤ) = k + 1 := by dsimp [N, k]; omega
  have hc : -((I.card - 2 : ℕ) : ℤ) = k := by dsimp [k]; omega
  let s := (serreConcreteCubeComplexFunctor A).map
    (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2))
      (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (N + 1)) hd).inv
  let f := simplexSubsetLambdaCell A I hI
  let g := F.map a b
  let t := (s ≫ f) ≫ g
  have hC : (cubicalLambdaNativeSimplexData A F).hom I
      (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
      k hI rfl rfl rfl =
      eqToHom (congrArg H.X hk) (serreCubeTopCellImage A H (N + 1) t) :=
    (cubicalLambdaNativeSimplexData_hom_normalized A F I _ _ k hI rfl rfl rfl).trans
      (serreCubeTopCellImage_cast_dimension_post A hd.symm k hk hc f g).symm
  let B (i : Fin (N + 1)) := ((i.val : ℤ) + 1).negOnePow •
    (eqToHom (congrArg H.X ht)
        (serreCubeTopCellImage A H N ((serreCubeFace A false N i).hom ≫ t)) -
      eqToHom (congrArg H.X ht)
        (serreCubeTopCellImage A H N ((serreCubeFace A true N i).hom ≫ t)))
  have hD : differential A ((cubicalLambdaNativeSimplexData A F).hom I
      (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
      k hI rfl rfl rfl) = ∑ i, B i :=
    (congrArg (fun w => H.d k (k + 1) w) hC).trans
      (serreCubeTopCellImage_cast_d A H N k hk ht t)
  let e : Fin (I.card - 2) ≃ Fin (N + 1) :=
    { toFun := Fin.cast hd
      invFun := Fin.cast hd.symm
      left_inv := fun _ => Fin.ext rfl
      right_inv := fun _ => Fin.ext rfl }
  have he := e.sum_comp B
  exact hD.trans (he.symm.trans (Finset.sum_congr rfl (fun i _ => by
    have hF (v : Bool) :
        eqToHom (congrArg H.X ht)
          (serreCubeTopCellImage A H N ((serreCubeFace A v N (e i)).hom ≫ t)) =
        simplexSubsetUniformFaceTopImage A v F I hI h3 i :=
      congrArg (fun l => eqToHom (congrArg H.X ht) (serreCubeTopCellImage A H N l))
        (Category.assoc (serreCubeFace A v N (e i)).hom (s ≫ f) g).symm
    exact congrArg₂ (fun x y => ((i.val : ℤ) + 1).negOnePow • (x - y)) (hF false) (hF true))))

end SerrePositivity.KST.SConstruction
