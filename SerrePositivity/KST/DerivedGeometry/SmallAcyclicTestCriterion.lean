module

public import SerrePositivity.KST.DerivedGeometry.LargerAcyclicCokernel
public import SerrePositivity.KST.DerivedGeometry.AcyclicSubobjectIteration
public import SerrePositivity.KST.DerivedGeometry.HomotopyOrthogonalTransfinite
public import SerrePositivity.KST.DerivedGeometry.HomotopyOrthogonalIso

/-!
概要：構成した小さい非輪状試験族による非有界 K-injective 判定。
方針：任意の非輪状複体を小さい試験商を加える連続超限列で尽くし、互換な零ホモトピーを貼る。
規約：試験集合・超限分解の存在は証明済みの具体的構成を使う。
使われ方：Stacks Lemma 19.12.3、TT §3・§8、Toën §3.2 の非有界 K-injective 分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits ZeroObject
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/--
概要：試験族への直交性は、選んだ非輪状拡大の余核への直交性を与える。
方針：余核が零の場合と試験対象に同型な場合に分ける。
規約：各項 injectivity はこの移送だけには不要。
使われ方：Stacks 19.12.3、TT §3 の超限列の後続商。
-/
lemma largerAcyclicSubobject_cokernel_orthogonal (G : C) (hG : IsSeparator G)
    (M : CochainComplex C ℤ) (hM : M.Acyclic) (S : Subobject M)
    (hS : (S : CochainComplex C ℤ).Acyclic) (I : CochainComplex C ℤ)
    (hI : ∀ (s : SmallAcyclicTestIndex G) (f : smallAcyclicTestFamily G s ⟶ I),
      Nonempty (Homotopy f 0))
    (f : cokernel (Subobject.ofLE S (largerAcyclicSubobject G hG M hM S)
      (le_largerAcyclicSubobject G hG M hM S)) ⟶ I) : Nonempty (Homotopy f 0) := by
  obtain h | ⟨s, ⟨e⟩⟩ := largerAcyclicSubobject_cokernel G hG M hM S hS
  · exact ⟨Homotopy.ofEq (h.eq_zero_of_src f)⟩
  · exact homotopy_orthogonal_of_iso e (hI s) f

/--
概要：各項 injective で小さい非輪状試験族に直交する複体は非有界 K-injective。
方針：部分対象格子の超限反復で任意の非輪状複体を尽くし、後続商の直交性を使う。
規約：小さい試験族と到達整列長の存在を仮定せず構成する。
使われ方：Stacks 19.12.3、TT §3・§8、Toën §3.2 の非有界導来比較。
-/
lemma isKInjective_of_smallAcyclicTests (G : C) (hG : IsSeparator G)
    (I : CochainComplex C ℤ) [∀ n, Injective (I.X n)]
    (hI : ∀ (s : SmallAcyclicTestIndex G) (f : smallAcyclicTestFamily G s ⟶ I),
      Nonempty (Homotopy f 0)) : I.IsKInjective where
  nonempty_homotopy_zero {M} f hM := by
    let φ := largerAcyclicSubobject G hG M hM
    let hφ := le_largerAcyclicSubobject G hG M hM
    have hzero : ((⊥ : Subobject M) : CochainComplex C ℤ).Acyclic :=
      HomologicalComplex.acyclic_of_isZero _ ((isZero_zero _).of_iso Subobject.botCoeIsoZero)
    obtain ⟨o, j, hj⟩ := subobjectIteration_exists_ordinal φ (⊥ : Subobject M)
      (lt_largerAcyclicSubobject G hG M hM) (largerAcyclicSubobject_top G hG M hM)
    have : Nonempty o.ToType := ⟨j⟩
    have := WellFoundedLT.toOrderBot o.ToType
    let F₀ := subobjectIterationFunctor φ hφ (⊥ : Subobject M) o.ToType
    let F := (Set.initialSegIic j).monotone.functor ⋙ F₀
    let c := coconeOfDiagramTerminal (isTerminalTop : IsTerminal (⊤ : Set.Iic j)) F
    have hc : IsColimit c := colimitOfDiagramTerminal isTerminalTop F
    have hbot : IsZero (F.obj ⊥) := by
      change IsZero (((transfiniteIterate φ (⊥ : o.ToType) (⊥ : Subobject M)) : Subobject M) :
        CochainComplex C ℤ)
      rw [transfiniteIterate_bot]
      exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
    have h₀ : ∀ g : F.obj ⊥ ⟶ I, Nonempty (Homotopy g 0) :=
      fun g => ⟨Homotopy.ofEq (hbot.eq_zero_of_src g)⟩
    have hm : ∀ (k : Set.Iic j) (_ : ¬IsMax k), Mono (F.map (homOfLE (Order.le_succ k))) := by
      intro k hk
      change Mono (Subobject.ofLE _ _ _)
      infer_instance
    have hq : ∀ (k : Set.Iic j) (_ : ¬IsMax k)
        (g : cokernel (F.map (homOfLE (Order.le_succ k))) ⟶ I), Nonempty (Homotopy g 0) := by
      intro k hk g
      let S : Subobject M := transfiniteIterate φ k.val ⊥
      let S' : Subobject M := transfiniteIterate φ (Order.succ k).val ⊥
      have hS : (S : CochainComplex C ℤ).Acyclic := acyclic_subobject_transfiniteIterate φ hφ
        (largerAcyclicSubobject_acyclic G hG M hM) ⊥ hzero k.val
      have heq : S' = φ S := by
        dsimp [S', S]
        rw [Set.Iic.succ_eq_of_not_isMax hk,
          transfiniteIterate_succ φ _ _ (Set.not_isMax_coe _ hk)]
      let E : cokernel (F.map (homOfLE (Order.le_succ k))) ≅
          cokernel (Subobject.ofLE S (φ S) (hφ S)) :=
        subobjectInclusionCokernelIsoOfEq S S' (φ S) heq
          (monotone_transfiniteIterate φ ⊥ hφ (show k.val ≤ (Order.succ k).val from
            leOfHom ((Set.initialSegIic j).monotone.functor.map (homOfLE (Order.le_succ k)))))
          (hφ S)
      exact homotopy_orthogonal_of_iso E
        (largerAcyclicSubobject_cokernel_orthogonal G hG M hM S hS I hI) g
    have hfinal : ∀ g : c.pt ⟶ I, Nonempty (Homotopy g 0) :=
      homotopy_orthogonal_transfinite c hc I hm h₀ hq
    let S : Subobject M := transfiniteIterate φ j ⊥
    have : IsIso S.arrow := (Subobject.isIso_arrow_iff_eq_top S).mpr hj
    let E : c.pt ≅ M := asIso S.arrow
    exact homotopy_orthogonal_of_iso E.symm hfinal f

end SerrePositivity.KST.DerivedGeometry
