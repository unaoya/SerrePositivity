import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.DegenerateHornInput
import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonTriangleDegeneracy
import Lean.Util.CollectAxioms

universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

section Prescribed
variable (K : SSet.{v}) {n : ℕ} (i : Fin (n + 2))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))
  {S : SSet.{v}} (b : S ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K) [Mono b]
  (a : S ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj K)
  (ha : a ≫ KanHornFamilyLifting.restriction K i = b)

example : RelativeHornFillingOperation.section_ K i hK b a ha ≫
    KanHornFamilyLifting.restriction K i = 𝟙 _ :=
  RelativeHornFillingOperation.section_restriction K i hK b a ha
example {U : SSet.{v}} (j : U ⟶ S) :
    RelativeHornFillingOperation.fill K i hK b a ha (j ≫ b) = j ≫ a :=
  RelativeHornFillingOperation.fill_prescribed K i hK b a ha j
-- Parameter maps in the uniform operation need not be monomorphisms.
example {U L : SSet.{v}} (j : U ⟶ L)
    (c : L ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K) :
    RelativeHornFillingOperation.family K i hK b a ha (j ≫ c) =
      SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁ j ≫
        RelativeHornFillingOperation.family K i hK b a ha c :=
  RelativeHornFillingOperation.family_naturality K i hK b a ha c j
end Prescribed

section Degenerate
variable (K : SSet.{v}) {n : ℕ} (i : Fin (n + 2)) (d : Fin (n + 1))
example : Mono (DegenerateHornInput.boundary i d K) := inferInstance
example : DegenerateHornInput.boundary i d K ≫ DegenerateHornInput.recover i d K = 𝟙 _ :=
  DegenerateHornInput.boundary_recover i d K
example (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) {L : SSet.{v}}
    (a : L ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K) :
    uncurry (a ≫ DegenerateHornInput.boundary i d K ≫ DegenerateHornInput.section_ i d K hK) =
      SSet.stdSimplex.σ d ▷ L ≫ uncurry a :=
  DegenerateHornInput.family_degeneracy i d K hK a
end Degenerate

-- A previous actual degenerate comparison triangle is retained as a whole simplex.
example {T K : SSet.{v}} {f z : T ⟶ K} (F : SSet.Homotopy f z)
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) :
    let Q := (ihom T).obj K
    let hQ := SimplexParameterHom.native_kan T K hK
    RelativeChoiceSpace.name (ComparisonTriangleDegeneracy.diagonal F).triangle ≫
      KanHornFamilyLifting.restriction Q (2 : Fin 3) ≫
        DegenerateHornInput.section_ (2 : Fin 3) (0 : Fin 2) Q hQ =
          RelativeChoiceSpace.name (ComparisonTriangleDegeneracy.diagonal F).triangle := by
  dsimp only
  have hn : RelativeChoiceSpace.name (ComparisonTriangleDegeneracy.diagonal F).triangle =
      RelativeChoiceSpace.name (curry F.h) ≫ DegenerateHornInput.degeneracy (0 : Fin 2)
        ((ihom T).obj K) := (RelativeChoiceSpace.name_precomp _ _).symm
  rw [hn]
  simp only [Category.assoc]
  exact congrArg (fun q => RelativeChoiceSpace.name (curry F.h) ≫ q)
    (DegenerateHornInput.section_degeneracy (2 : Fin 3) (0 : Fin 2) ((ihom T).obj K)
      (SimplexParameterHom.native_kan T K hK))

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeHornFillingOperation,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.DegenerateHornInput]
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
  unless modules.size == expected.size do throwError "Missing relative horn operation modules"
  logInfo m!"Relative horn operation audit passed: {count} declarations in {modules.size} modules."
