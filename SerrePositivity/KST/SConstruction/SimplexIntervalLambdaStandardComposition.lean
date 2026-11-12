module
public import SerrePositivity.KST.SConstruction.SimplexIntervalSerreComposition
public import SerrePositivity.KST.SConstruction.SimplexIntervalComposeStandardSerre
public import SerrePositivity.KST.SConstruction.SerreCubeTensorCompositionTransport

/-! # 元の標準区間 Hom 同型と実 Λ 合成
概要：元の三区間 Hom 比較は、標準区間次元の同じ実合成 cube を回収する。
方針：元の Serre 生成射の実合成と、左右・和次元の等号移送の tensor 保存を照合する。
規約：元の全 Hom 同型と実合成を保持。使われ方：native HA 逆 Hom の合成保存。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の三区間 Hom 同型の実 tensor 合成は、標準次元の元の合成 cube を回収する。 -/
lemma simplexIntervalLambdaHomIso_composition {N : ℕ} (a b c : Fin (N + 1))
    (hab : a < b) (hbc : b < c) :
    serreCubeTensorComposition A (b.val - a.val - 1) (c.val - b.val - 1)
        (simplexIntervalLambdaHomIso A a b hab.le).hom
        (simplexIntervalLambdaHomIso A b c hbc.le).hom =
      (serreConcreteCubeComplexFunctor A).map
        (simplexIntervalComposeStandardCube.{u} a b c hab hbc) ≫
          (simplexIntervalLambdaHomIso A a c (hab.le.trans hbc.le)).hom := by
  let n := b.val - a.val - 1
  let m := c.val - b.val - 1
  let T := necklaceBead.{u} (b.val - a.val)
  let U := necklaceBead.{u} (c.val - b.val)
  let V := necklaceBead.{u} (c.val - a.val)
  let F := serreConcreteCubeComplexFunctor A
  let L := necklaceLambdaCell A (necklaceInSimplexInterval.{u} a b hab.le)
  let R := necklaceLambdaCell A (necklaceInSimplexInterval.{u} b c hbc.le)
  let H := necklaceLambdaCell A (necklaceInSimplexInterval.{u} a c (hab.le.trans hbc.le))
  have hn := (necklaceBead_dimension.{u} (b.val - a.val)).symm
  have hm := (necklaceBead_dimension.{u} (c.val - b.val)).symm
  let es := concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n + m))
    (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (T.down.dimension + U.down.dimension)) (congrArg₂ Nat.add hn hm)
  let et := concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (c.val - a.val - 1))
    (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk V.down.dimension) (necklaceBead_dimension.{u} (c.val - a.val)).symm
  have hdim : F.map es.hom =
      eqToHom (congrArg (serreCubeComplex A) (congrArg₂ Nat.add hn hm)) :=
    serreCubeComplexMap_dimension_inv A (congrArg₂ Nat.add hn hm).symm
  have htarget : F.map et.hom ≫ H =
      (simplexIntervalLambdaHomIso A a c (hab.le.trans hbc.le)).hom := by
    have hd : F.map et.hom = eqToHom (congrArg (serreCubeComplex A)
        (necklaceBead_dimension.{u} (c.val - a.val)).symm) :=
      serreCubeComplexMap_dimension_inv A (necklaceBead_dimension.{u} (c.val - a.val))
    exact (congrArg (fun f => f ≫ H) hd).trans
      (simplexIntervalLambdaHomIso_cell A a c (hab.le.trans hbc.le)).symm
  have hc : es.hom ≫ (necklaceCubeTensorIso T U).hom ≫
      necklaceConcreteCubeMap (simplexIntervalComposeBeadHom.{u} a b c hab.le hbc.le) =
      simplexIntervalComposeStandardCube.{u} a b c hab hbc ≫ et.hom := by
    have hd := concreteCubeDimensionIso_hom_trans (congrArg₂ Nat.add hn hm)
      (T.down.wedge_dimension U.down).symm
    have he : es.hom ≫ (necklaceCubeTensorIso T U).hom =
        (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n + m))
          (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T U).down.dimension)
          (simplexIntervalCompose_source_dimension.{u} a b c)).hom := hd
    rw [← Category.assoc, he]
    unfold simplexIntervalComposeStandardCube
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hcmap : F.map es.hom ≫ F.map (necklaceCubeTensorIso T U).hom ≫
      F.map (necklaceConcreteCubeMap
        (simplexIntervalComposeBeadHom.{u} a b c hab.le hbc.le)) =
      F.map (simplexIntervalComposeStandardCube.{u} a b c hab hbc) ≫ F.map et.hom := by
    have h := congrArg F.map hc
    simpa only [Functor.map_comp, Category.assoc] using h
  have h₀ : serreCubeTensorComposition A n m
      (simplexIntervalLambdaHomIso A a b hab.le).hom
      (simplexIntervalLambdaHomIso A b c hbc.le).hom =
      eqToHom (congrArg (serreCubeComplex A) (congrArg₂ Nat.add hn hm)) ≫
        serreCubeTensorComposition A T.down.dimension U.down.dimension L R :=
    (congrArg₂ (fun f g => serreCubeTensorComposition A n m f g)
      (simplexIntervalLambdaHomIso_cell A a b hab.le)
      (simplexIntervalLambdaHomIso_cell A b c hbc.le)).trans
        (serreCubeTensorComposition_dimension A hn hm L R)
  have h₁ := simplexIntervalLambdaCell_composition A a b c hab.le hbc.le
  have h₂ := congrArg (fun f => F.map es.hom ≫ f) h₁
  have h₃ := congrArg (fun f => f ≫ H) hcmap
  exact h₀.trans ((congrArg (fun f => f ≫
    serreCubeTensorComposition A T.down.dimension U.down.dimension L R) hdim.symm).trans
      (h₂.trans (((Category.assoc _ _ _).symm.trans h₃).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun f => F.map
            (simplexIntervalComposeStandardCube.{u} a b c hab hbc) ≫ f) htarget)))))

/-- 元の三区間 Hom 同型の実合成は、元の HA と同じ右一面を回収する。 -/
lemma simplexIntervalLambdaHomIso_composition_one_tensor {N : ℕ}
    (a b c : Fin (N + 1)) (hab : a < b) (hbc : b < c) :
    serreCubeTensorComposition A (b.val - a.val - 1) (c.val - b.val - 1)
        (simplexIntervalLambdaHomIso A a b hab.le).hom
        (simplexIntervalLambdaHomIso A b c hbc.le).hom =
      (serreCubeRightFace A true (b.val - a.val - 1) (c.val - b.val - 1)).hom ≫
        eqToHom (congrArg (serreCubeComplex A)
          (simplexHAStrictInterval_split_dimension a b c hab hbc).symm) ≫
          (simplexIntervalLambdaHomIso A a c (hab.le.trans hbc.le)).hom :=
  (simplexIntervalLambdaHomIso_composition A a b c hab hbc).trans
    ((congrArg (fun f => f ≫ (simplexIntervalLambdaHomIso A a c
      (hab.le.trans hbc.le)).hom) (simplexIntervalComposeStandardCube_serre A a b c hab hbc)).trans
        (Category.assoc _ _ _))

end SerrePositivity.KST.SConstruction
