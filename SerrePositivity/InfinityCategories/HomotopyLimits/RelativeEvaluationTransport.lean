module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningParametrizedTransport
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationTransportNaturality
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorComposition

/-!
概要：相対 Hom の全評価は、底の辺に沿う両端の輸送と可換になる。
方針：相対射の全空間をパラメータに残した二つの prism を同じ始点で比較する。
規約：各相対射の点ごとの比較を自然な族とは仮定しない。
使われ方：Yoneda 恒等点評価の、元の有限余積の各脚に関する自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 同じ fiber の普遍相対評価を元の全空間へ含めた式。 -/
lemma relativeFunctorFiberEvaluation_inclusion {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (a : B _⦋0⦌) :
    relativeFunctorFiberEvaluation p q a ≫ vertexFiberι q a =
      (vertexFiberι p a ▷ relativeFunctorSpace q p) ≫
        relativeFunctorEvaluation (Over.mk p) (Over.mk q) := rfl

/-- 同じ指定点を全相対 Hom の族に入れた評価は、fiber Hom の同じ点での評価。 -/
lemma relativeFunctorFiberEvaluation_point {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (a : B _⦋0⦌) (v : (vertexFiber p a) _⦋0⦌) :
    lift (SSet.const v) (𝟙 (relativeFunctorSpace q p)) ≫
        relativeFunctorFiberEvaluation p q a =
      relativeFunctorFiberHom p q a ≫ evaluateFunctorAt v := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply Subtype.ext
  rfl

/-- 相対 Hom 全体の評価は、元の底の同じ辺に沿う両端の輸送と関手同型まで可換。 -/
def relativeFunctorEvaluation_transportIso {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    {a b : B _⦋0⦌} (e : SSet.Edge a b) :
    FunctorIso
      ((edgeTransport p e ▷ relativeFunctorSpace q p) ≫
        relativeFunctorFiberEvaluation p q b)
      (relativeFunctorFiberEvaluation p q a ≫ edgeTransport q e) := by
  let R := relativeFunctorSpace q p
  let A := vertexFiber p a
  let L := A ⊗ R
  let H := (edgeTransport_isTransport p e).choose
  have hH₀ := (edgeTransport_isTransport p e).choose_spec.1
  have hH₁ := (edgeTransport_isTransport p e).choose_spec.2.1
  have hHp := (edgeTransport_isTransport p e).choose_spec.2.2.1
  let K := (edgeTransport_isTransport q e).choose
  have hK₀ := (edgeTransport_isTransport q e).choose_spec.1
  have hK₁ := (edgeTransport_isTransport q e).choose_spec.2.1
  have hKp := (edgeTransport_isTransport q e).choose_spec.2.2.1
  let β := fst (Δ[1] : SSet.{u}) L ≫ SSet.yonedaEquiv.symm e.edge
  let W := (α_ (Δ[1] : SSet.{u}) A R).inv ≫ H ▷ R ≫
    relativeFunctorEvaluation (Over.mk p) (Over.mk q)
  let W' := (Δ[1] ◁ relativeFunctorFiberEvaluation p q a) ≫ K
  have hEval : relativeFunctorEvaluation (Over.mk p) (Over.mk q) ≫ q =
      fst E R ≫ p := relativeFunctorEvaluation_projection (Over.mk p) (Over.mk q)
  have hW : W ≫ q = β := by
    dsimp only [W, β]
    rw [Category.assoc, Category.assoc,
      hEval,
      ← Category.assoc (H ▷ R), whiskerRight_fst, Category.assoc, hHp]
    rfl
  have hW' : W' ≫ q = β := by
    dsimp only [W', β]
    rw [Category.assoc, hKp, ← Category.assoc, whiskerLeft_fst]
    rfl
  have hW₀ : prismEndpoint 0 L ≫ W =
      relativeFunctorFiberEvaluation p q a ≫ vertexFiberι q a := by
    dsimp only [W, L]
    rw [← Category.assoc, ← Category.assoc, fiberTransportFamily_reassociate_endpoint]
    change ((prismEndpoint 0 A ▷ R) ≫ H ▷ R) ≫ _ = _
    rw [← comp_whiskerRight, hH₀]
    exact (relativeFunctorFiberEvaluation_inclusion p q a).symm
  have hW₀' : prismEndpoint 0 L ≫ W' =
      relativeFunctorFiberEvaluation p q a ≫ vertexFiberι q a := by
    dsimp only [W']
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hK₀]
  have hW₁ : prismEndpoint 1 L ≫ W =
      ((edgeTransport p e ▷ R) ≫ relativeFunctorFiberEvaluation p q b) ≫
        vertexFiberι q b := by
    dsimp only [W, L]
    rw [← Category.assoc, ← Category.assoc, fiberTransportFamily_reassociate_endpoint]
    change ((prismEndpoint 1 A ▷ R) ≫ H ▷ R) ≫ _ = _
    rw [← comp_whiskerRight, hH₁, comp_whiskerRight, Category.assoc]
    simpa only [Category.assoc] using congrArg
      (fun z ↦ (edgeTransport p e ▷ R) ≫ z)
      (relativeFunctorFiberEvaluation_inclusion p q b).symm
  have hW₁' : prismEndpoint 1 L ≫ W' =
      (relativeFunctorFiberEvaluation p q a ≫ edgeTransport q e) ≫ vertexFiberι q b := by
    dsimp only [W']
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hK₁, Category.assoc]
  let i := scaffoldFirstVertex 1 ▷ L
  let v := snd (Δ[0] : SSet.{u}) L ≫ relativeFunctorFiberEvaluation p q a ≫ vertexFiberι q a
  have hWi : i ≫ W = v := by
    dsimp only [i, v]
    rw [scaffoldFirstVertex_whiskerRight, Category.assoc]
    exact congrArg (fun z ↦ snd (Δ[0] : SSet.{u}) L ≫ z) hW₀
  have hWi' : i ≫ W' = v := by
    dsimp only [i, v]
    rw [scaffoldFirstVertex_whiskerRight, Category.assoc]
    exact congrArg (fun z ↦ snd (Δ[0] : SSet.{u}) L ≫ z) hW₀'
  have hv : v ≫ q = i ≫ β := by rw [← hWi, Category.assoc, hW]
  have hj : prismEndpoint 1 L ≫ β = SSet.const b :=
    (prismEdgeFamily_one e.edge).trans (congrArg (fun z ↦ (SSet.const z : L ⟶ B)) e.tgt_eq)
  exact relativeExtensionFiberEndpoint_witnessIso q β i
    (simplexPrismFirstVertex_leftAnodyne 1 L) v hv (prismEndpoint 1 L) b hj
    W W' hW hW' hWi hWi' _ _ hW₁ hW₁'

end SerrePositivity.InfinityCategories.HomotopyLimits
