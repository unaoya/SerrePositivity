module
public import SerrePositivity.KST.SConstruction.Cofinality.CoreFlagSupply

/-!
概要：元の S 構成の全辺 wide 単体を全 Ar 成分で検出する。
方針：各元の辺に分母の全成分判定を適用し、評価の元の自然性で順序を交換する。
規約：同じ元の単体と全辺条件を保持する。
使われ方：相対 S 旗の転置を同じ wide 旗へ持ち上げる条件。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：次段の元の wide 単体の所属は全 Ar 評価後の元の wide 所属と同値。
方針：同じ元の全辺を取り、分母辺の全 Ar 判定と評価の自然性を使う。
規約：先頭方向と元の反復 S 多次数を同時に保持する。
使われ方：相対旗の S 交換の全単体条件。 -/
lemma completionSWideSimplex_iff_pointwise (m r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (d : SimplexCategory)
    (v : (sStableModel m (((multiSEndofunctor r).obj ι).obj Y)).carrier.obj (Opposite.op d)) :
    v ∈ (LocalizingInvariants.completionCofiberWide
        ((sEndofunctor m).map (((multiSEndofunctor r).obj ι).map f)).val).obj (Opposite.op d) ↔
      ∀ a : (arNerve m) _⦋0⦌,
        (sStableEvaluation m (((multiSEndofunctor r).obj ι).obj Y) a).val.app (Opposite.op d) v ∈
          (LocalizingInvariants.completionCofiberWide
            (((multiSEndofunctor r).obj ι).map f).val).obj (Opposite.op d) := by
  constructor
  · intro hv a θ
    let E := sStableEvaluation m (((multiSEndofunctor r).obj ι).obj Y) a
    have h := (completionSWideEdge_iff_pointwise m r ι f hf
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((sStableModel m (((multiSEndofunctor r).obj ι).obj Y)).carrier.map
        θ.op v))).mp (hv θ) a
    have he := ConcreteCategory.congr_hom (E.val.naturality θ.op) v
    exact (congrArg (fun t => t ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      (LocalizingInvariants.completionEssentialImage (((multiSEndofunctor r).obj ι).map f).val))
        he).mp h
  · intro hv θ
    apply (completionSWideEdge_iff_pointwise m r ι f hf
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((sStableModel m (((multiSEndofunctor r).obj ι).obj Y)).carrier.map
        θ.op v))).mpr
    intro a
    let E := sStableEvaluation m (((multiSEndofunctor r).obj ι).obj Y) a
    have he := ConcreteCategory.congr_hom (E.val.naturality θ.op) v
    exact (congrArg (fun t => t ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      (LocalizingInvariants.completionEssentialImage (((multiSEndofunctor r).obj ι).map f).val))
        he).mpr (hv a θ)

end SerrePositivity.KST.SConstruction.Cofinality
