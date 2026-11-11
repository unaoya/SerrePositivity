module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullTrianglePrismDiagonals
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalVertices
/-!
概要：元上下全比較の共有対角候補を、元両端固定の実区間写像空間の族へ置く。
方針：元恒等端点経路を定値に回収し、既存の区間模型の curry を使う。
規約：元の対角ホモトピーの全射を厳密回収。二候補の一致は別工程。
使われ方：同じ零成分の Hom 比較を元実対角比較へ接続する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
private lemma nullDiagonalIdentityConstant (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 A)).edge =
      (SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A) : (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) := by
  change SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) (𝟙 A)).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  change (SSet.Truncated.Edge.id (X := (truncation 2).obj _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u})
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A)).edge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A) 1
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _).symm
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
/-- 概要：元下対角候補の両端は同じ元核・元商の定値族。
方針：元の恒等経路回収を標準零単体の単位射で評価する。
規約：元全一単体の等号。使われ方：同じ固定端点区間模型への入力。 -/
lemma dgOdotMilnorNuNullLowerDiagonalHomotopy_endpoints :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u + 2}) ≫
        (dgOdotMilnorNuNullLowerDiagonalHomotopy R d h).h = SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (K)) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u + 2}) ≫
        (dgOdotMilnorNuNullLowerDiagonalHomotopy R d h).h = SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (B)) := by
  let s : (Δ[1] : SSet.{u + 2}) ⟶ Δ[0] ⊗ Δ[1] :=
    lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 Δ[1])
  constructor
  · calc
      _ = s ≫ (stdSimplex.δ (1 : Fin 2) ▷ Δ[1]) ≫
          (dgOdotMilnorNuNullLowerDiagonalHomotopy R d h).h := rfl
      _ = s ≫ snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (K : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge :=
        congrArg (fun q => s ≫ q) (dgOdotMilnorNuNullLowerDiagonalHomotopy_paths R d h).1
      _ = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (K : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge := by
        rw [← Category.assoc, lift_snd, Category.id_comp]
      _ = _ := nullDiagonalIdentityConstant (K)
  · calc
      _ = s ≫ (stdSimplex.δ (0 : Fin 2) ▷ Δ[1]) ≫
          (dgOdotMilnorNuNullLowerDiagonalHomotopy R d h).h := rfl
      _ = s ≫ snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge :=
        congrArg (fun q => s ≫ q) (dgOdotMilnorNuNullLowerDiagonalHomotopy_paths R d h).2
      _ = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge := by
        rw [← Category.assoc, lift_snd, Category.id_comp]
      _ = _ := nullDiagonalIdentityConstant (B)
/-- 概要：元下全比較の対角候補を同じ両端固定区間写像空間の実族へ置く。
方針：同じ元定値二端点から既存の区間模型の curry を取る。
規約：元二対角辺と全ホモトピーを保持。使われ方：元実対角比較の Hom 内表現。 -/
def dgOdotMilnorNuNullLowerDiagonalIntervalParameter :
    (Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (K)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (B)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints (dgOdotMilnorNuNullLowerDiagonalHomotopy R d h).h
    (dgOdotMilnorNuNullLowerDiagonalHomotopy_endpoints R d h).1
    (dgOdotMilnorNuNullLowerDiagonalHomotopy_endpoints R d h).2
/-- 概要：同じ元下対角区間族の展開は元対角ホモトピーの全射。
方針：既存の同じ端点付き curry の往復を使う。
規約：全単体の厳密等号。使われ方：元共有対角の全比較の保持。 -/
lemma dgOdotMilnorNuNullLowerDiagonalIntervalParameter_uncurry :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgOdotMilnorNuNullLowerDiagonalIntervalParameter R d h) =
      (dgOdotMilnorNuNullLowerDiagonalHomotopy R d h).h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints _ _ _
/-- 概要：元下対角区間族は元実／絶対対角辺そのものを両端に持つ。
方針：同じ元ホモトピーの二端点と元対角辺の全回収を使う。
規約：元の二実辺。使われ方：同じ Hom 比較での元両端点の固定。 -/
lemma dgOdotMilnorNuNullLowerDiagonalIntervalParameter_faces :
    stdSimplex.δ (1 : Fin 2) ≫ dgOdotMilnorNuNullLowerDiagonalIntervalParameter R d h =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuNullDiagonalMap R d))) ∧
      stdSimplex.δ (0 : Fin 2) ≫ dgOdotMilnorNuNullLowerDiagonalIntervalParameter R d h =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuAbsoluteDiagonalMap R d h))) := by
  constructor
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, dgOdotMilnorNuNullLowerDiagonalIntervalParameter_uncurry,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge_uncurry]
    have hs : ((Δ[1] : SSet.{u + 2}) ◁ stdSimplex.δ (1 : Fin 2)) =
        fst Δ[1] Δ[0] ≫ (ι₀ : (Δ[1] : SSet.{u + 2}) ⟶ Δ[1] ⊗ Δ[1]) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [whiskerLeft_fst]
        change fst (Δ[1] : SSet.{u + 2}) Δ[0] =
          fst Δ[1] Δ[0] ≫ ι₀ ≫ fst Δ[1] Δ[1]
        rw [ι₀_fst, Category.comp_id]
      · rw [whiskerLeft_snd]
        change snd (Δ[1] : SSet.{u + 2}) Δ[0] ≫ stdSimplex.δ (_ : Fin 2) =
          fst Δ[1] Δ[0] ≫ ι₀ ≫ snd Δ[1] Δ[1]
        rw [ι₀_snd, stdSimplex.δ_one_eq_const, SSet.comp_const,
          SSet.comp_const]
    rw [hs, Category.assoc, SSet.Homotopy.h₀, dgOdotMilnorNuNullDiagonalMap_diagram]
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, dgOdotMilnorNuNullLowerDiagonalIntervalParameter_uncurry,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge_uncurry]
    have hs : ((Δ[1] : SSet.{u + 2}) ◁ stdSimplex.δ (0 : Fin 2)) =
        fst Δ[1] Δ[0] ≫ (ι₁ : (Δ[1] : SSet.{u + 2}) ⟶ Δ[1] ⊗ Δ[1]) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [whiskerLeft_fst]
        change fst (Δ[1] : SSet.{u + 2}) Δ[0] =
          fst Δ[1] Δ[0] ≫ ι₁ ≫ fst Δ[1] Δ[1]
        rw [ι₁_fst, Category.comp_id]
      · rw [whiskerLeft_snd]
        change snd (Δ[1] : SSet.{u + 2}) Δ[0] ≫ stdSimplex.δ (_ : Fin 2) =
          fst Δ[1] Δ[0] ≫ ι₁ ≫ snd Δ[1] Δ[1]
        rw [ι₁_snd, stdSimplex.δ_zero_eq_const, SSet.comp_const,
          SSet.comp_const]
    rw [hs, Category.assoc, SSet.Homotopy.h₁, dgOdotMilnorNuAbsoluteDiagonalMap_diagram]
/-- 概要：元上対角候補の両端は同じ元核・元商の定値族。
方針：元の恒等経路回収を標準零単体の単位射で評価する。
規約：元全一単体の等号。使われ方：同じ固定端点区間模型への入力。 -/
lemma dgOdotMilnorNuNullUpperDiagonalHomotopy_endpoints :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u + 2}) ≫
        (dgOdotMilnorNuNullUpperDiagonalHomotopy R d h).h = SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (K)) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u + 2}) ≫
        (dgOdotMilnorNuNullUpperDiagonalHomotopy R d h).h = SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (B)) := by
  let s : (Δ[1] : SSet.{u + 2}) ⟶ Δ[0] ⊗ Δ[1] :=
    lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 Δ[1])
  constructor
  · calc
      _ = s ≫ (stdSimplex.δ (1 : Fin 2) ▷ Δ[1]) ≫
          (dgOdotMilnorNuNullUpperDiagonalHomotopy R d h).h := rfl
      _ = s ≫ snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (K : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge :=
        congrArg (fun q => s ≫ q) (dgOdotMilnorNuNullUpperDiagonalHomotopy_paths R d h).1
      _ = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (K : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge := by
        rw [← Category.assoc, lift_snd, Category.id_comp]
      _ = _ := nullDiagonalIdentityConstant (K)
  · calc
      _ = s ≫ (stdSimplex.δ (0 : Fin 2) ▷ Δ[1]) ≫
          (dgOdotMilnorNuNullUpperDiagonalHomotopy R d h).h := rfl
      _ = s ≫ snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge :=
        congrArg (fun q => s ≫ q) (dgOdotMilnorNuNullUpperDiagonalHomotopy_paths R d h).2
      _ = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge := by
        rw [← Category.assoc, lift_snd, Category.id_comp]
      _ = _ := nullDiagonalIdentityConstant (B)
/-- 概要：元上全比較の対角候補を同じ両端固定区間写像空間の実族へ置く。
方針：同じ元定値二端点から既存の区間模型の curry を取る。
規約：元二対角辺と全ホモトピーを保持。使われ方：元実対角比較の Hom 内表現。 -/
def dgOdotMilnorNuNullUpperDiagonalIntervalParameter :
    (Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (K)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (B)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints (dgOdotMilnorNuNullUpperDiagonalHomotopy R d h).h
    (dgOdotMilnorNuNullUpperDiagonalHomotopy_endpoints R d h).1
    (dgOdotMilnorNuNullUpperDiagonalHomotopy_endpoints R d h).2
/-- 概要：同じ元上対角区間族の展開は元対角ホモトピーの全射。
方針：既存の同じ端点付き curry の往復を使う。
規約：全単体の厳密等号。使われ方：元共有対角の全比較の保持。 -/
lemma dgOdotMilnorNuNullUpperDiagonalIntervalParameter_uncurry :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgOdotMilnorNuNullUpperDiagonalIntervalParameter R d h) =
      (dgOdotMilnorNuNullUpperDiagonalHomotopy R d h).h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints _ _ _
/-- 概要：元上対角区間族は元実／絶対対角辺そのものを両端に持つ。
方針：同じ元ホモトピーの二端点と元対角辺の全回収を使う。
規約：元の二実辺。使われ方：同じ Hom 比較での元両端点の固定。 -/
lemma dgOdotMilnorNuNullUpperDiagonalIntervalParameter_faces :
    stdSimplex.δ (1 : Fin 2) ≫ dgOdotMilnorNuNullUpperDiagonalIntervalParameter R d h =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuNullDiagonalMap R d))) ∧
      stdSimplex.δ (0 : Fin 2) ≫ dgOdotMilnorNuNullUpperDiagonalIntervalParameter R d h =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuAbsoluteDiagonalMap R d h))) := by
  constructor
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, dgOdotMilnorNuNullUpperDiagonalIntervalParameter_uncurry,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge_uncurry]
    have hs : ((Δ[1] : SSet.{u + 2}) ◁ stdSimplex.δ (1 : Fin 2)) =
        fst Δ[1] Δ[0] ≫ (ι₀ : (Δ[1] : SSet.{u + 2}) ⟶ Δ[1] ⊗ Δ[1]) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [whiskerLeft_fst]
        change fst (Δ[1] : SSet.{u + 2}) Δ[0] =
          fst Δ[1] Δ[0] ≫ ι₀ ≫ fst Δ[1] Δ[1]
        rw [ι₀_fst, Category.comp_id]
      · rw [whiskerLeft_snd]
        change snd (Δ[1] : SSet.{u + 2}) Δ[0] ≫ stdSimplex.δ (_ : Fin 2) =
          fst Δ[1] Δ[0] ≫ ι₀ ≫ snd Δ[1] Δ[1]
        rw [ι₀_snd, stdSimplex.δ_one_eq_const, SSet.comp_const,
          SSet.comp_const]
    rw [hs, Category.assoc, SSet.Homotopy.h₀, dgOdotMilnorNuNullDiagonalMap_diagram]
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, dgOdotMilnorNuNullUpperDiagonalIntervalParameter_uncurry,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge_uncurry]
    have hs : ((Δ[1] : SSet.{u + 2}) ◁ stdSimplex.δ (0 : Fin 2)) =
        fst Δ[1] Δ[0] ≫ (ι₁ : (Δ[1] : SSet.{u + 2}) ⟶ Δ[1] ⊗ Δ[1]) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [whiskerLeft_fst]
        change fst (Δ[1] : SSet.{u + 2}) Δ[0] =
          fst Δ[1] Δ[0] ≫ ι₁ ≫ fst Δ[1] Δ[1]
        rw [ι₁_fst, Category.comp_id]
      · rw [whiskerLeft_snd]
        change snd (Δ[1] : SSet.{u + 2}) Δ[0] ≫ stdSimplex.δ (_ : Fin 2) =
          fst Δ[1] Δ[0] ≫ ι₁ ≫ snd Δ[1] Δ[1]
        rw [ι₁_snd, stdSimplex.δ_zero_eq_const, SSet.comp_const,
          SSet.comp_const]
    rw [hs, Category.assoc, SSet.Homotopy.h₁, dgOdotMilnorNuAbsoluteDiagonalMap_diagram]
end SerrePositivity.KST.SConstruction
