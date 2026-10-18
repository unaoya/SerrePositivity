module

public import SerrePositivity.KST.DerivedGeometry.RingedFreeCech

/-!
概要：任意の環層上で任意の開被覆の自由増大 Čech が完全な分解を与える。
方針：被覆内の収縮と被覆外の零を基礎アーベル群の局所層化判定で大域化する。
規約：環層の可換性・平坦性や被覆の有限性を要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の実際の係数加群層圏での分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable (X : TopCat.{u}) (B : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/--
概要：V に含まれない開で評価した V 内の形式的余積の自由加群前層は零。
方針：各 Hom の空性により B(W) 上の自由加群が零となることを使う。
規約：係数は固定環でなく実際の B(W)。
使われ方：TT §3、Toën §3.2 の増大 Čech の被覆外の計算。
-/
lemma ringedFreeFormalPresheaf_isZero_outside (S : FormalCoproduct.{u} (Opens X))
    (V W : Opens X) (hS : ∀ i, S.obj i ≤ V) (hWV : ¬ W ≤ V) :
    IsZero ((((FormalCoproduct.eval (Opens X) (PresheafOfModules.{u} B.obj)).obj
      (ringedFreePresheafOnOpen X B)).obj S).obj (.op W)) := by
  apply IsZero.of_iso _ ((ringedFreeFormalPresheafEvaluationIso X B W).app S)
  change IsZero (∐ fun i : S.I => (ModuleCat.free (B.obj.obj (.op W))).obj (W ⟶ S.obj i))
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Sigma.hom_ext
  intro i
  have : IsEmpty (W ⟶ S.obj i) := ⟨fun f => hWV ((leOfHom f).trans (hS i))⟩
  have : Subsingleton ((ModuleCat.free (B.obj.obj (.op W))).obj (W ⟶ S.obj i)) :=
    inferInstanceAs (Subsingleton ((W ⟶ S.obj i) →₀ B.obj.obj (.op W)))
  exact (ModuleCat.isZero_of_subsingleton _).eq_of_src _ _

variable {ι : Type u} (U : ι → Opens X) (V : Opens X) (hU : ∀ i, U i ≤ V)

/--
概要：被覆先に含まれない開で評価した環層係数の自由増大 Čech の各項は零。
方針：各有限交叉の被覆先への包含と空の表現可能基底を使う。
規約：零項の増大先も含めて証明する。
使われ方：TT §3、Toën §3.2 の係数版分解の局所完全性。
-/
lemma ringedFreePresheafAugmentedCech_isZero_outside
    (W : Opens X) (hWV : ¬ W ≤ V) (n : ℕ) :
    IsZero ((ringedFreePresheafAugmentedCechComplex X B U V hU).X n |>.obj (.op W)) := by
  cases n with
  | zero =>
    exact ringedFreeFormalPresheaf_isZero_outside X B
      ((FormalCoproduct.incl (Opens X)).obj V) V W (fun _ => le_rfl) hWV
  | succ n =>
    apply ringedFreeFormalPresheaf_isZero_outside X B _ V W _ hWV
    intro t
    exact (leOfHom (Pi.π (fun a : Fin (n + 1) => U (t a)) 0)).trans (hU (t 0))

/--
概要：環層係数の自由加群前層の増大 Čech を実際の加群層に層化した鎖複体。
方針：元の環層上の加群層化を全次数へ適用する。
規約：基礎アーベル群だけの代理対象でなく実際の B 加群層。
使われ方：TT §3・§8、Toën §3.2 の係数 Ext の自由 Čech 分解。
-/
def ringedFreeSheafAugmentedCechComplex : ChainComplex (SheafOfModules.{u} B) ℕ :=
  ((PresheafOfModules.sheafification (𝟙 B.obj)).mapHomologicalComplex (.down ℕ)).obj
    (ringedFreePresheafAugmentedCechComplex X B U V hU)

/--
概要：任意の開 V の任意の被覆の自由 B 加群層の増大 Čech は全次数で完全。
方針：評価時の局所収縮と被覆外の零を基礎層化へ移し、忠実完全な忘却で反映する。
規約：平坦性・可換性・被覆の有限性を一切仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数版の有限次元移動。
-/
lemma ringedFreeSheafAugmentedCech_acyclic (hcover : (⨆ i, U i) = V) :
    (ringedFreeSheafAugmentedCechComplex X B U V hU).Acyclic := by
  intro n
  apply (ringed_exact_iff_toSheaf X B _).mpr
  change (((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
    (.down ℕ)).obj
      (((PresheafOfModules.toPresheaf B.obj).mapHomologicalComplex (.down ℕ)).obj
        (ringedFreePresheafAugmentedCechComplex X B U V hU))).ExactAt n
  apply abSheafification_exactAt_of_locally_exactAt
  intro W x hx
  by_cases hxV : x ∈ V
  · have hxc : x ∈ (⨆ i, U i) := by rw [hcover]; exact hxV
    obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp hxc
    refine ⟨W ⊓ U j, inf_le_left, ⟨hx, hxj⟩, ?_⟩
    exact (ringedFreePresheafAugmentedCech_evaluated_exactAt X B U V hU
      (W ⊓ U j) j inf_le_right n).map
        (forget₂ (ModuleCat.{u} (B.obj.obj (.op (W ⊓ U j)))) AddCommGrpCat.{u})
  · refine ⟨W, le_rfl, hx, ?_⟩
    have hz := ringedFreePresheafAugmentedCech_isZero_outside X B U V hU W
      (fun h => hxV (h hx)) n
    exact ShortComplex.exact_of_isZero_X₂ _
      (Functor.map_isZero (forget₂ (ModuleCat.{u} (B.obj.obj (.op W))) AddCommGrpCat.{u}) hz)

end SerrePositivity.KST.DerivedGeometry
