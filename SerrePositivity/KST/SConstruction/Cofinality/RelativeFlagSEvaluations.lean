module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeSSimplexDetection

/-!
概要：元の相対 S 旗の転置は全 Ar 評価を回収する。
方針：gapped 持ち上げの包含公式と元の内部 Hom の評価公式を合成する。
規約：同じ元の包含と評価の射の等号として保持する。
使われ方：転置した旗の全分母条件と逆向きの交換の照合。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の相対 S 転置は包含後に生の転置を回収する。
方針：同じ gapped 族の持ち上げの包含公式を使う。
規約：元の全高次単体の等号。
使われ方：元の Ar 評価の回収。 -/
lemma completionRelativeSTransposeDiagram_inclusion (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory) :
    completionRelativeSTransposeDiagram r ι f hf m n ≫
      (ihom (stdSimplex.obj n)).map (gappedSubcomplex m
        (((multiSEndofunctor r).obj ι).obj Y).carrier).ι =
      completionRelativeSRawTranspose r ι f hf m n := by
  apply uncurry_injective
  exact (uncurry_natural_right (completionRelativeSTransposeDiagram r ι f hf m n)
    (gappedSubcomplex m (((multiSEndofunctor r).obj ι).obj Y).carrier).ι).trans
      ((congrArg (fun h => h ≫
        (gappedSubcomplex m (((multiSEndofunctor r).obj ι).obj Y).carrier).ι)
          (uncurry_curry (gappedFamilyLift
            (uncurry (completionRelativeSRawTranspose r ι f hf m n))
            (completionRelativeSRawTranspose_gapped r ι f hf m n)))).trans
              (gappedFamilyLift_ι _ _))

/-- 概要：転置後の全 Ar 評価は転置前の元の相対旗の評価に一致する。
方針：同じ内部 Hom の交換後の評価と元の後合成評価を照合する。
規約：元の全部分旗包含への射の等号。
使われ方：元の転置旗の wide 条件の全成分判定。 -/
lemma completionRelativeSTransposeDiagram_evaluation (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory)
    (a : (arNerve m) _⦋0⦌) :
    completionRelativeSTransposeDiagram r ι f hf m n ≫
      (ihom (stdSimplex.obj n)).map
        (sStableEvaluation m (((multiSEndofunctor r).obj ι).obj Y) a).val =
      (sStableEvaluation m (completionRelativeFlagStableModel r ι f hf n) a).val ≫
        (completionRelativeFlagAmbientMap r ι f hf n).val := by
  let T := completionRelativeSTransposeDiagram r ι f hf m n
  let J := (gappedSubcomplex m (((multiSEndofunctor r).obj ι).obj Y).carrier).ι
  let E := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (((multiSEndofunctor r).obj ι).obj Y).carrier) a
  have he : (ihom (stdSimplex.obj n)).map
      (sStableEvaluation m (((multiSEndofunctor r).obj ι).obj Y) a).val =
        (ihom (stdSimplex.obj n)).map J ≫ (ihom (stdSimplex.obj n)).map E :=
    (ihom (stdSimplex.obj n)).map_comp J E
  calc
    _ = T ≫ ((ihom (stdSimplex.obj n)).map J ≫ (ihom (stdSimplex.obj n)).map E) :=
      congrArg (fun h => T ≫ h) he
    _ = (T ≫ (ihom (stdSimplex.obj n)).map J) ≫ (ihom (stdSimplex.obj n)).map E :=
      (Category.assoc _ _ _).symm
    _ = completionRelativeSRawTranspose r ι f hf m n ≫
        (ihom (stdSimplex.obj n)).map E :=
      congrArg (fun h => h ≫ (ihom (stdSimplex.obj n)).map E)
        (completionRelativeSTransposeDiagram_inclusion r ι f hf m n)
    _ = _ := by
      let G := (gappedSubcomplex m (completionRelativeFlagStableModel r ι f hf n).carrier).ι
      let I := (completionRelativeFlagAmbientMap r ι f hf n).val
      let H := (ihom (arNerve m)).map I
      let S := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (arNerve m) (stdSimplex.obj n)
        (((multiSEndofunctor r).obj ι).obj Y).carrier).hom
      change (G ≫ H ≫ S) ≫ (ihom (stdSimplex.obj n)).map E =
        (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) ≫ I
      let V := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (Y := (ihom (stdSimplex.obj n)).obj
          (((multiSEndofunctor r).obj ι).obj Y).carrier) a
      let L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (Y := (completionRelativeFlagStableModel r ι f hf n).carrier) a
      have hs : S ≫ (ihom (stdSimplex.obj n)).map E = V :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_evaluate (arNerve m) (stdSimplex.obj n)
          (((multiSEndofunctor r).obj ι).obj Y).carrier a
      have hi : H ≫ V = L ≫ I := ihom_postcomp_evaluate I a
      exact (Category.assoc G (H ≫ S)
        ((ihom (stdSimplex.obj n)).map E)).trans
          ((congrArg (fun h => G ≫ h)
            ((Category.assoc H S ((ihom (stdSimplex.obj n)).map E)).trans
              ((congrArg (fun h => H ≫ h) hs).trans hi))).trans
                (Category.assoc G L I).symm)

end SerrePositivity.KST.SConstruction.Cofinality
