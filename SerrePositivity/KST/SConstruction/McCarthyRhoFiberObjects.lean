module
public import SerrePositivity.KST.SConstruction.McCarthyFiberCoordinates
public import SerrePositivity.KST.SConstruction.McCarthyRhoEvaluations

/-! # McCarthy の ρ の object S 値の単体的な族
概要：左 fiber の図式と時刻の単体から ρ の gapped 図式を作り、射に束ねる。
方針：元の C 内の ρ の自然性を object S の単体作用に移す。
規約：未証明の fiber 条件を入力にしない。使われ方：左 fiber 内の実ホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：標準単体の制限は対応する順序写像の前合成。
方針：各有限順序の点で計算する。
規約：全ての単体作用素。使われ方：ρ の添字の自然性。 -/
lemma simplexOrder_map {m n l : ℕ} (σ : ⦋l⦌ ⟶ ⦋n⦌)
    (p : (Δ[m] : SSet.{u}) _⦋n⦌) :
    (stdSimplex.objEquiv ((Δ[m] : SSet.{u}).map σ.op p)).toOrderHom =
      (stdSimplex.objEquiv p).toOrderHom.comp σ.toOrderHom := by
  ext i
  rfl

/-- 概要：ρ は入力図式・添字・時刻の等号を保つ。
方針：入力の等号を消去し、条件の証明の違いを忘れる。
規約：左 fiber の条件もそれぞれの入力に対するもの。使われ方：依存する入力の自然性。 -/
lemma mcCarthyRho_congr {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C)
    {α α' : Fin (n + 1) →o Fin (m + 1)} {τ τ' : Fin (n + 1) →o Fin 2}
    {E E' : arNerve n ⟶ cofiberDiagrams C}
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A)
    (h' : E' ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α' ≫ A) (hα : α = α') (hτ : τ = τ') (hE : E = E') :
    mcCarthyRho z A α τ E h = mcCarthyRho z A α' τ' E' h' := by
  subst α'
  subst τ'
  subst E'
  rfl

/-- 概要：左 fiber の単体と時刻から元の ρ の gapped 図式の単体を作る。
方針：固定単体の最後の対角を零対象として使い、証明済みの gapped 性を添える。
規約：出力の選択を追加しない。使われ方：実ホモトピーの各単体。 -/
def mcCarthyRhoFiberObjectVertex (X : StableModel.{u}) {m n : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌)
    (τ : (Δ[1] : SSet.{u}) _⦋n⦌) : (objectSConstruction (cofiberDiagrams X.carrier)) _⦋n⦌ :=
  gappedObjectVertex
    (mcCarthyRho (objectSLastDiagonalZeroVertex a) (gappedDiagram a)
      (stdSimplex.objEquiv (mcCarthyFiberParameter X a e)).toOrderHom
      (stdSimplex.objEquiv τ).toOrderHom (mcCarthyFiberDiagram X a e)
        (mcCarthyFiberDiagram_source X a e))
    (mcCarthyRho_isGapped (objectSLastDiagonalZeroVertex a) (gappedDiagram a)
      (gappedDiagram_isGapped a) _ _ (mcCarthyFiberDiagram X a e)
      (gappedDiagram_isGapped _) (mcCarthyFiberDiagram_source X a e))

/-- 概要：ρ の候補単体の実図式は元の C 内で選んだ ρ。
方針：gapped 図式と object S の頂点の往復の式。
規約：図式全体の等号。使われ方：自然性と fiber 条件。 -/
lemma mcCarthyRhoFiberObjectVertex_diagram (X : StableModel.{u}) {m n : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌)
    (τ : (Δ[1] : SSet.{u}) _⦋n⦌) :
    gappedDiagram (mcCarthyRhoFiberObjectVertex X a e τ) =
      mcCarthyRho (objectSLastDiagonalZeroVertex a) (gappedDiagram a)
        (stdSimplex.objEquiv (mcCarthyFiberParameter X a e)).toOrderHom
        (stdSimplex.objEquiv τ).toOrderHom (mcCarthyFiberDiagram X a e)
          (mcCarthyFiberDiagram_source X a e) :=
  gappedDiagram_gappedObjectVertex _ _

/-- 概要：ρ の族を object S 値の実際の単体的射に束ねる。
方針：Ar の全前合成との厳密な自然性を使う。
規約：全ての面・退化を含む。使われ方：左 fiber への持ち上げ。 -/
def mcCarthyRhoFiberObjectMap (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    cofiberSubobjectLeftFiber X a ⊗ Δ[1] ⟶ objectSConstruction (cofiberDiagrams X.carrier) where
  app n := ↾fun p => mcCarthyRhoFiberObjectVertex X a p.1 p.2
  naturality {n l} σ := by
    rcases n with ⟨⟨n⟩⟩
    rcases l with ⟨⟨l⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨e, τ⟩
    apply gappedDiagram_injective
    symm
    change gappedDiagram ((objectSConstruction (cofiberDiagrams X.carrier)).map σ
      (mcCarthyRhoFiberObjectVertex X a e τ)) =
        gappedDiagram (mcCarthyRhoFiberObjectVertex X a
          ((cofiberSubobjectLeftFiber X a).map σ e) ((Δ[1] : SSet.{u}).map σ τ))
    rw [gappedDiagram_objectS_map, mcCarthyRhoFiberObjectVertex_diagram,
      mcCarthyRhoFiberObjectVertex_diagram]
    have hE := mcCarthyFiberDiagram_map X a e σ.unop
    have hα := mcCarthyFiberParameter_map X a e σ.unop
    change mcCarthyFiberDiagram X a ((cofiberSubobjectLeftFiber X a).map σ e) =
      arNerveMap σ.unop.toOrderHom ≫ mcCarthyFiberDiagram X a e at hE
    change mcCarthyFiberParameter X a ((cofiberSubobjectLeftFiber X a).map σ e) =
      (Δ[m] : SSet.{u}).map σ (mcCarthyFiberParameter X a e) at hα
    have hαord : (stdSimplex.objEquiv
        ((Δ[m] : SSet.{u}).map σ (mcCarthyFiberParameter X a e))).toOrderHom =
        (stdSimplex.objEquiv (mcCarthyFiberParameter X a e)).toOrderHom.comp
          σ.unop.toOrderHom := simplexOrder_map σ.unop (mcCarthyFiberParameter X a e)
    have hc : (arNerveMap σ.unop.toOrderHom ≫ mcCarthyFiberDiagram X a e) ≫
        cofiberProjection X.carrier ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
          (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        arNerveMap ((stdSimplex.objEquiv (mcCarthyFiberParameter X a e)).toOrderHom.comp
          σ.unop.toOrderHom) ≫ gappedDiagram a := by
      have h := mcCarthyFiberDiagram_source X a ((cofiberSubobjectLeftFiber X a).map σ e)
      simpa only [hE, hα, hαord] using h
    exact ((mcCarthyRho_pre (objectSLastDiagonalZeroVertex a) (gappedDiagram a)
      (stdSimplex.objEquiv (mcCarthyFiberParameter X a e)).toOrderHom
      (stdSimplex.objEquiv τ).toOrderHom (mcCarthyFiberDiagram X a e)
      (mcCarthyFiberDiagram_source X a e) σ.unop.toOrderHom hc).symm).trans
        (mcCarthyRho_congr _ _ hc (mcCarthyFiberDiagram_source X a
          ((cofiberSubobjectLeftFiber X a).map σ e))
          (by rw [hα]; exact hαord.symm) (simplexOrder_map σ.unop τ).symm hE.symm)

end SerrePositivity.KST.SConstruction
