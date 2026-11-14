module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechFrameLift
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechFrameComparison
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.BigCechAlexander
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.BigCechAffineEnvelope
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.Site.PrismOver

/-!
# 大きい prismatic 枠から有限枠への比較

## 概要
完備多項式の各元を有限枠の第 0 項に持ち上げ、大きい枠から有限枠への余単体的な射を作る。

## 方針
各頂点の射で持ち上げをその頂点へ送り、包の普遍性で延長する。

## 規約
持ち上げは各多項式対象について選ぶ。比較は余単体方向で厳密に自然。

## 使われ方
BS 著者版 Remark 4.19 の表示の比較の逆向きの射。
-/

public noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.BigCechFrameRetraction

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (Q : Poly (A ⧸ P.ideal)) {κ : Cardinal.{u}}
variable (U : ∀ n, AffineEnvelopeTerm P Q.n n κ)
variable (X : ∀ (Q' : Poly (A ⧸ P.ideal)) n, BigCechTerm P Q' n)

private def liftZero (a : polyCompletion P Q.n) : (U 0).X.B :=
  (Ideal.Quotient.mk_surjective ((U 0).X.sec a)).choose

private theorem liftZero_spec (a : polyCompletion P Q.n) :
    Ideal.Quotient.mk (U 0).X.Q.ideal (liftZero P Q U a) = (U 0).X.sec a :=
  (Ideal.Quotient.mk_surjective ((U 0).X.sec a)).choose_spec

private def vertex (n : ℕ) (i : Fin (n + 1)) : (U 0).X ⟶ (U n).X :=
  affineTermMap P (U 0) (U n) (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)

private def values (n : ℕ) (s : BigCechIndex P Q n) : (U n).X.B :=
  (vertex P Q U n s.2).toHom.toRingHom (liftZero P Q U s.1)

private theorem values_mod (n : ℕ) (s : BigCechIndex P Q n) :
    Ideal.Quotient.mk (U n).X.Q.ideal (values P Q U n s) = (U n).X.sec s.1 := by
  unfold values
  rw [← OrientedPrism.Hom.quotientMap_mk, liftZero_spec]
  exact RingHom.congr_fun (vertex P Q U n s.2).comm_sec s.1

private theorem values_map {m n : SimplexCategory} (θ : m ⟶ n) (s : BigCechIndex P Q m.len) :
    (affineTermMap P (U m.len) (U n.len) θ).toHom.toRingHom (values P Q U m.len s) =
      values P Q U n.len (s.1, θ.toOrderHom s.2) := by
  let F := cechAlexanderOfAffineTerms P U
  have h : vertex P Q U m.len s.2 ≫ affineTermMap P (U m.len) (U n.len) θ =
      vertex P Q U n.len (θ.toOrderHom s.2) := by
    change F.map (SimplexCategory.const ⦋0⦌ m s.2) ≫ F.map θ =
      F.map (SimplexCategory.const ⦋0⦌ n (θ.toOrderHom s.2))
    rw [← F.map_comp, SimplexCategory.const_comp]
  exact congrArg (fun a : (U 0).X ⟶ (U n.len).X =>
    a.toHom.toRingHom (liftZero P Q U s.1)) h

private def liftAt (n : ℕ) : (X Q n).carrier →+* (U n).X.B :=
  ((X Q n).existsUnique_liftVariables (U n).X.Q (U n).X.toHom (U n).X.sec (U n).X.sec_comp
    (values P Q U n) (values_mod P Q U n)).choose

private theorem liftAt_spec (n : ℕ) :
    (X Q n).prism.deltaStructure.IsDeltaHom (U n).X.Q.deltaStructure (liftAt P Q U X n) ∧
      (liftAt P Q U X n).comp (X Q n).base.toRingHom = (U n).X.toHom.toRingHom ∧
      ∀ s, liftAt P Q U X n ((X Q n).variableImage s) = values P Q U n s :=
  ((X Q n).existsUnique_liftVariables (U n).X.Q (U n).X.toHom (U n).X.sec (U n).X.sec_comp
    (values P Q U n) (values_mod P Q U n)).choose_spec.1

private theorem liftAt_naturality {m n : SimplexCategory} (θ : m ⟶ n) :
    (liftAt P Q U X n.len).comp ((X Q m.len).map (X Q n.len) (𝟙 Q) θ.toOrderHom) =
      (affineTermMap P (U m.len) (U n.len) θ).toHom.toRingHom.comp (liftAt P Q U X m.len) := by
  let t := affineTermMap P (U m.len) (U n.len) θ
  let w (s : BigCechIndex P Q m.len) := values P Q U n.len (s.1, θ.toOrderHom s.2)
  have hw (s : BigCechIndex P Q m.len) :
      Ideal.Quotient.mk (U n.len).X.Q.ideal (w s) = (U n.len).X.sec s.1 :=
    values_mod P Q U n.len (s.1, θ.toOrderHom s.2)
  have h := (X Q m.len).existsUnique_liftVariables (U n.len).X.Q (U n.len).X.toHom
    (U n.len).X.sec (U n.len).X.sec_comp w hw
  apply h.unique
  · refine ⟨(liftAt_spec P Q U X n.len).1.comp
      ((X Q m.len).map_isDeltaHom (X Q n.len) (𝟙 Q) θ.toOrderHom), ?_, ?_⟩
    · rw [RingHom.comp_assoc, (X Q m.len).map_base, (liftAt_spec P Q U X n.len).2.1]
    · intro s
      rw [RingHom.comp_apply, (X Q m.len).map_variableImage, (liftAt_spec P Q U X n.len).2.2]
      simp only [w, BigCechTerm.indexMap, polyCompletionMap_id, AlgHom.id_apply]
  · refine ⟨t.toHom.map_delta.comp (liftAt_spec P Q U X m.len).1, ?_, ?_⟩
    · rw [RingHom.comp_assoc, (liftAt_spec P Q U X m.len).2.1]
      exact congrArg OrientedPrism.Hom.toRingHom t.comm_base
    · intro s
      rw [RingHom.comp_apply, (liftAt_spec P Q U X m.len).2.2]
      exact values_map P Q U θ s

/-- 選んだ持ち上げが定める、大きい枠から有限枠への余単体的代数の射。 -/
def _root_.SerrePositivity.BhattScholze.Prismatic.bigCechToAffineFrame :
    (bigCechAlexanderOfTerms P X).obj Q ⟶ polyCosimplicialAlgebraOfAffineTerms P U where
  app n := Under.homMk (CommRingCat.ofHom (liftAt P Q U X n.len))
    (CommRingCat.hom_ext (liftAt_spec P Q U X n.len).2.1)
  naturality {m n} θ := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    exact liftAt_naturality P Q U X θ

end SerrePositivity.BhattScholze.Prismatic.BigCechFrameRetraction
