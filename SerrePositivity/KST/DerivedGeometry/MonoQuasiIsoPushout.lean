module

public import SerrePositivity.KST.DerivedGeometry.AcyclicCokernelQuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-!
概要：非有界複体の単射準同型は押し出しで保たれる。
方針：単射の準同型性を余核の非輪状性で判定し、押し出しで余核が同型となることを使う。
規約：任意のアーベル圏。平坦性や有界性は不要。
使われ方：Stacks 19.12.4・19.12.6、TT §3・§8、Toën §3.2 の cell 付加。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C]

/--
概要：複体の単射とその余核の短複体。
方針：複体の圏で余核を取る。
規約：実際の余核対象を使用する。
使われ方：Stacks 19.12.4、TT §3 の単射準同型の判定。
-/
def monoCokernelShortComplex {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk f (cokernel.π f) (cokernel.condition f)

/--
概要：単射とその余核の短複体は短完全。
方針：余核の普遍性と元の単射性を使う。
規約：非有界複体。
使われ方：Stacks 19.12.4、TT §3 の余核のコホモロジー。
-/
lemma monoCokernelShortComplex_shortExact {K L : CochainComplex C ℤ} (f : K ⟶ L) [Mono f] :
    (monoCokernelShortComplex f).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)
  mono_f := by change Mono f; infer_instance
  epi_g := by change Epi (cokernel.π f); infer_instance

/--
概要：単射な鎖写像は余核が非輪状であることと準同型性が同値。
方針：短完全列の長完全列を両方向に使う。
規約：次数の制限は不要。
使われ方：Stacks 19.12.4・19.12.6、TT §3 の付加の準同型性。
-/
lemma mono_quasiIso_iff_acyclic_cokernel {K L : CochainComplex C ℤ} (f : K ⟶ L) [Mono f] :
    QuasiIso f ↔ (cokernel f).Acyclic :=
  ⟨fun hf => (monoCokernelShortComplex_shortExact f).acyclic_X₃ hf,
    fun h => shortExact_quasiIso_f_of_acyclic _ (monoCokernelShortComplex_shortExact f) h⟩

/--
概要：単射準同型の押し出しは準同型。
方針：単射性の保存と余核の比較同型で非輪状性を移す。
規約：実際の押し出し正方形での主張。
使われ方：Stacks 19.12.4・19.12.6、TT §3・§8、Toën §3.2 の非有界 cell 付加。
-/
lemma quasiIso_of_isPushout_of_mono
    {A B E F : CochainComplex C ℤ} {i : A ⟶ B} {j : A ⟶ E} {k : B ⟶ F} {l : E ⟶ F}
    (sq : IsPushout i j k l) [Mono i] [QuasiIso i] : QuasiIso l := by
  have : Mono l := (MorphismProperty.monomorphisms (CochainComplex C ℤ)).of_isPushout sq.flip inferInstance
  have hi := (mono_quasiIso_iff_acyclic_cokernel i).mp inferInstance
  have : IsIso (cokernel.map i l j k sq.w) := isIso_cokernel_map_of_isPushout sq
  apply (mono_quasiIso_iff_acyclic_cokernel l).mpr
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hi n).isZero_homology.of_iso
    ((HomologicalComplex.homologyFunctor C (.up ℤ) n).mapIso (asIso (cokernel.map i l j k sq.w)).symm)

end SerrePositivity.KST.DerivedGeometry
