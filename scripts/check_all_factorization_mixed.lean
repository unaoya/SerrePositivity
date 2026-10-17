import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

section GeneralParameters
variable {P : SSet.{v}} (hp : UniverseLift.BoundaryFillers P) {K : SSet.{max w v}}
  {A B C D : K ⟶ UniverseLift.obj.{w} P}
  (AB : SSet.Homotopy A B) (BD : SSet.Homotopy B D)
  (AC : SSet.Homotopy A C) (CD : SSet.Homotopy C D)

-- All four prescribed maps on the whole parameter K are retained; no model on large SSet.
example : K ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    LargeParameterSquare.triangle hp AB BD AC CD true = AB.h :=
  LargeParameterSquare.left_first hp AB BD AC CD
example : K ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    LargeParameterSquare.triangle hp AB BD AC CD true = BD.h :=
  LargeParameterSquare.left_second hp AB BD AC CD
example : K ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    LargeParameterSquare.triangle hp AB BD AC CD false = AC.h :=
  LargeParameterSquare.right_first hp AB BD AC CD
example : K ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    LargeParameterSquare.triangle hp AB BD AC CD false = CD.h :=
  LargeParameterSquare.right_second hp AB BD AC CD
example : K ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
    LargeParameterSquare.triangle hp AB BD AC CD true =
      K ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ LargeParameterSquare.triangle hp AB BD AC CD false :=
  LargeParameterSquare.common_diagonal hp AB BD AC CD
end GeneralParameters

section ArbitraryModel
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {X' X Y V W : ResolutionObject C} (a : X' ⟶ X) (f : X.base ⟶ Y.base)
  (g : Y ⟶ V) (b : V ⟶ W) (φ : ResolutionLiftPrecomposition.FrameMap a)

-- Strict transport squares are equalities of actual maps, with independent object/Hom universes.
example : CoherentLiftMixedComparison.mapBD hcof X' X Y V a f g φ ≫
    AllFactorizationMixedTransport.choiceMap hcof a f g b φ =
    CoherentLiftPostComposition.firstMap hcof X' Y V W (a.base ≫ f) g b ≫
      CoherentLiftMixedComparison.mapBD hcof X' X Y W a f (g ≫ b) φ :=
  AllFactorizationMixedTransport.mapBD_tail hcof a f g b φ
example : CoherentLiftMixedComparison.mapAC X' X Y V a f g φ ≫
    AllFactorizationMixedTransport.choiceMap hcof a f g b φ =
    CoherentLiftPostComposition.firstMap hcof X Y V W f g b ≫
      CoherentLiftMixedComparison.mapAC X' X Y W a f (g ≫ b) φ :=
  AllFactorizationMixedTransport.mapAC_tail hcof a f g b φ

-- The four old global homotopies are retained, after their specified actual transports.
example : AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    AllFactorizationMixed.triangle hcof hfib a f g b φ true =
      (AllFactorizationPost.homotopy hcof hfib (a.base ≫ f) g b).h ≫ UniverseLift.map
        (CoherentLiftMixedComparison.mapBD hcof X' X Y W a f (g ≫ b) φ) :=
  AllFactorizationMixed.triangle_AB hcof hfib a f g b φ
example : AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    AllFactorizationMixed.triangle hcof hfib a f g b φ true =
      (AllFactorizationPre.homotopy hcof hfib a f g φ).h ≫
        AllFactorizationMixed.valueMap hcof a f g b φ :=
  AllFactorizationMixed.triangle_BD hcof hfib a f g b φ
example : AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    AllFactorizationMixed.triangle hcof hfib a f g b φ false =
      AllFactorizationMixed.chainMap g b ▷ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ≫
        (AllFactorizationPre.homotopy hcof hfib a f (g ≫ b) φ).h :=
  AllFactorizationMixed.triangle_AC hcof hfib a f g b φ
example : AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    AllFactorizationMixed.triangle hcof hfib a f g b φ false =
      (AllFactorizationPost.homotopy hcof hfib f g b).h ≫ UniverseLift.map
        (CoherentLiftMixedComparison.mapAC X' X Y W a f (g ≫ b) φ) :=
  AllFactorizationMixed.triangle_CD hcof hfib a f g b φ

-- The actual frame lift is available from ordinary model axioms; no factorization functor input.
example : AnchoredChain.simplicial g ⊗ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2) ⟶
    UniverseLift.obj.{u} (AllFactorizationMixed.choiceSpace a f g b
      (ResolutionLiftPrecomposition.lift a)) :=
  AllFactorizationMixed.triangle hcof hfib a f g b (ResolutionLiftPrecomposition.lift a) true

-- All finite values stay in the original Hom universe v.
example (left : Bool) {n : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2)).obj
      (Opposite.op (SimplexCategory.mk n))) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
      AllFactorizationMixed.choiceSpace a f g b φ :=
  AllFactorizationMixed.simplex hcof hfib a f g b φ left c t
end ArbitraryModel

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.LargeParameterSquare,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.MappingSpaceEdges,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.AllFactorizationMixedTransport,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.AllFactorizationMixed]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do
    throwError "Some mixed comparison modules were not audited"
  logInfo m!"Global mixed comparison audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
