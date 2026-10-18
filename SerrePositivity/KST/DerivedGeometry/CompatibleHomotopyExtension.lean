module

public import SerrePositivity.KST.DerivedGeometry.InjectiveHomotopyShortExact

/-!
概要：商での零ホモトピー直交性を使って、既存の零ホモトピーと互換な延長を構成する。
方針：商から戻した補正の成分は部分複体上で零となることを証明する。
規約：零ホモトピーの存在だけでなく、その全成分の制限等式を得る。
使われ方：Stacks Lemma 19.12.3 (079L)、TT §3・§8、Toën §3.2 の連続超限工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C]
  (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
  (I : CochainComplex C ℤ) [∀ n, Injective (I.X n)]
include hS

/--
概要：部分複体で指定した零ホモトピーを、全成分で一致するように延長できる。
方針：injective な成分延長に、商から戻した零ホモトピーを加える。
規約：商からの全射の零ホモトピー性のみを入力する。
使われ方：Stacks 19.12.3、TT §3 の超限列の互換な零ホモトピー。
-/
lemma exists_compatible_homotopy_extension
    (h₃ : ∀ f : S.X₃ ⟶ I, Nonempty (Homotopy f 0))
    (f : S.X₂ ⟶ I) (h : Homotopy (S.f ≫ f) 0) :
    ∃ (k : Homotopy f 0), ∀ i j, S.f.f i ≫ k.hom i j = h.hom i j := by
  classical
  have := hS.mono_f
  have := hS.epi_g
  let v := injectiveExtendedHomotopy S.f h
  let g : S.X₂ ⟶ I := Homotopy.nullHomotopicMap v
  let hg : Homotopy g 0 := Homotopy.nullHomotopy v (fun _ _ hij => ite_eq_right hij)
  have hfg : S.f ≫ g = S.f ≫ f := by
    rw [Homotopy.comp_nullHomotopicMap]
    have hv : (fun i j => S.f.f i ≫ v i j) = h.hom := by
      funext i j
      exact comp_injectiveExtendedHomotopy S.f h i j
    rw [hv]
    simpa using h.sub_eq_nullHomotopicMap.symm
  have hz : S.f ≫ (f - g) = 0 := by
    rw [Preadditive.comp_sub, hfg, sub_self]
  let d : S.X₃ ⟶ I := hS.exact.desc (f - g) hz
  have hd : S.g ≫ d = f - g := hS.exact.g_desc _ hz
  let hq := (h₃ d).some
  let hr : Homotopy (f - g) 0 :=
    { hom := fun i j => S.g.f i ≫ hq.hom i j
      zero i j hij := by rw [hq.zero i j hij, comp_zero]
      comm i := by simpa only [Homotopy.compLeft, hd, comp_zero] using (hq.compLeft S.g).comm i }
  let k : Homotopy f 0 :=
    { hom := hr.hom + hg.hom
      zero i j hij := by simp only [Pi.add_apply, hr.zero i j hij, hg.zero i j hij, add_zero]
      comm i := by simpa only [Homotopy.add, HomologicalComplex.add_f_apply, sub_add_cancel,
        HomologicalComplex.zero_f_apply, add_zero] using (hr.add hg).comm i }
  refine ⟨k, ?_⟩
  intro i j
  have hzero : S.f.f i ≫ S.g.f i = 0 := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f_apply] using
      congrArg (fun u => u.f i) S.zero
  change S.f.f i ≫ (S.g.f i ≫ hq.hom i j + v i j) = h.hom i j
  simp only [zero_add, Preadditive.comp_add, ← Category.assoc, hzero, zero_comp, zero_add]
  exact comp_injectiveExtendedHomotopy S.f h i j

end SerrePositivity.KST.DerivedGeometry
