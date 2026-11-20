module

public import SerrePositivity.AlgebraicGeometry.FibreAlgebraAssociatedPrime
public import SerrePositivity.AlgebraicGeometry.ProjectivityFromCompletion

/-!
概要：KST §5、Stacks 05FS の幾何学的整な代数の射影性の完備基底側。
方針：ファイバーの随伴素イデアルを拡大素イデアルと同定し、Jacobson 根基の条件から 05DP を使う。
規約：一般の 05FS の Noether 帰納法・忠実平坦降下は別工程。
使われ方：局所化と完備化の被覆で代数の実分裂を構成する原典経路。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：Jacobson 根基に含まれるイデアルは、幾何学的整な代数の拡大素イデアルと和を取っても全体にならない。
方針：元の素イデアルを含む極大イデアルを選び、その拡大の素性を使う。
規約：KST §5、Stacks 05FS、基礎環は Noether、代数は平坦・有限表示・幾何学的整。
使われ方：完備基底上での 05DP のファイバー条件。
-/
theorem sup_extendedPrime_ne_top_of_le_jacobson
    (A B : Type u) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    (I : Ideal A) (hI : I ≤ (⊥ : Ideal A).jacobson) (p : Ideal A) [p.IsPrime] :
    I.map (algebraMap A B) ⊔ p.map (algebraMap A B) ≠ ⊤ := by
  obtain ⟨m, hm, hpm⟩ := p.exists_le_maximal Ideal.IsPrime.ne_top'
  let := hm
  have hIm : I ≤ m := hI.trans
    ((Ideal.jacobson_mono (bot_le : (⊥ : Ideal A) ≤ m)).trans_eq
      (Ideal.jacobson_eq_self_of_isMaximal (I := m)))
  have hsub : I.map (algebraMap A B) ⊔ p.map (algebraMap A B) ≤
      m.map (algebraMap A B) :=
    sup_le (Ideal.map_mono hIm) (Ideal.map_mono hpm)
  intro htop
  have hmTop : m.map (algebraMap A B) = ⊤ := top_unique (htop ▸ hsub)
  exact (ideal_map_isPrime_of_geometricallyIntegral A B m).ne_top hmTop

/--
概要：完備な Noether 基底上で、幾何学的整な平坦有限表示代数は最初の剰余が射影的なら射影的。
方針：ファイバーの随伴素イデアルと拡大素イデアルの一致、および中心の Jacobson 根基への包含を使う。
規約：KST §5、Stacks 05FS の完備化側。剰余の射影性は依然明示する。
使われ方：一般の 05FS の忠実平坦被覆の完備化側を処理する。
-/
theorem projective_geometricallyIntegral_of_complete_of_projective_reduction
    (A B : Type u) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    (I : Ideal A) [IsAdicComplete I A]
    [Module.Projective (A ⧸ I) (B ⧸ (I • (⊤ : Submodule A B)))] :
    Module.Projective A B := by
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  apply projective_of_complete_of_fibre_associatedPrimes A B B I
  intro p q hqp hq
  rw [associatedPrime_tensor_residueField_eq_extendedPrime A B p.asIdeal q hq]
  exact sup_extendedPrime_ne_top_of_le_jacobson A B I
    (IsAdicComplete.le_jacobson_bot I) p.asIdeal

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
