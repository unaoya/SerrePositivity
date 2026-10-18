module

public import SerrePositivity.KST.DerivedGeometry.CechExtCriterion

/-!
概要：任意の開を被覆する族の増大自由 Čech 分解。
方針：被覆内では追加退化を使い、被覆外では表現可能自由前層の切断が零となることを使う。
規約：空間全体の被覆に限定せず、係数の平坦性も要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の基本開上の次元移動。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits TopologicalSpace Abelian
namespace SerrePositivity.KST.DerivedGeometry
variable (R : Type u) [Ring R] (X : TopCat.{u})

/--
概要：V に含まれる開の形式的余積の自由前層は、V に含まれない開で零。
方針：各表現可能の Hom が空であり、空の基底の自由加群が零であることを使う。
規約：形式的余積の添字の有限性を要求しない。
使われ方：TT §3、Toën §3.2 の被覆外の自由 Čech の局所完全性。
-/
lemma freeFormalPresheaf_isZero_outside (S : FormalCoproduct.{u} (Opens X))
    (V W : Opens X) (hS : ∀ i, S.obj i ≤ V) (hWV : ¬ W ≤ V) :
    IsZero ((((FormalCoproduct.eval (Opens X) ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)).obj
      (freeModulePresheafOnOpen R X)).obj S).obj (.op W)) := by
  apply IsZero.of_iso _ ((freeFormalPresheafEvaluationIso R X W).app S)
  change IsZero (∐ fun i : S.I => (ModuleCat.free R).obj (W ⟶ S.obj i))
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Sigma.hom_ext
  intro i
  have : IsEmpty (W ⟶ S.obj i) := ⟨fun f => hWV ((leOfHom f).trans (hS i))⟩
  have : Subsingleton ((ModuleCat.free R).obj (W ⟶ S.obj i)) :=
    inferInstanceAs (Subsingleton ((W ⟶ S.obj i) →₀ R))
  exact (ModuleCat.isZero_of_subsingleton ((ModuleCat.free R).obj (W ⟶ S.obj i))).eq_of_src _ _

variable {ι : Type u} (U : ι → Opens X) (V : Opens X) (hU : ∀ i, U i ≤ V)

/--
概要：V に含まれない開で評価した増大自由 Čech の各項は零。
方針：零項は V の自由前層、他の項は V に含まれる有限交叉の自由前層の余積。
規約：有限交叉には必ず少なくとも一つの被覆元がある。
使われ方：TT §3、Toën §3.2 の相対 Čech 分解。
-/
lemma freePresheafAugmentedCech_isZero_outside (W : Opens X) (hWV : ¬ W ≤ V) (n : ℕ) :
    IsZero (((freePresheafAugmentedCechComplex R X U V hU).X n).obj (.op W)) := by
  cases n with
  | zero =>
    exact freeFormalPresheaf_isZero_outside R X
      ((FormalCoproduct.incl (Opens X)).obj V) V W (fun _ => le_rfl) hWV
  | succ n =>
    apply freeFormalPresheaf_isZero_outside R X _ V W _ hWV
    intro t
    exact (leOfHom (Pi.π (fun a : Fin (n + 1) => U (t a)) 0)).trans (hU (t 0))

/--
概要：V の任意の開被覆に対し自由層の増大 Čech は全次数で完全。
方針：V 内では被覆元内の収縮、V 外では全項が零となる局所計算を層化する。
規約：全空間を被覆することや有限性は要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の基本開への適用。
-/
lemma relativeFreeSheafAugmentedCech_acyclic (hcover : (⨆ i, U i) = V) :
    (freeSheafAugmentedCechComplex R X U V hU).Acyclic := by
  intro n
  apply sheafification_exactAt_of_locally_exactAt
    (freePresheafAugmentedCechComplex R X U V hU) n
  intro W x hx
  by_cases hxV : x ∈ V
  · have hxc : x ∈ (⨆ i, U i) := by rw [hcover]; exact hxV
    obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp hxc
    refine ⟨W ⊓ U j, inf_le_left, ⟨hx, hxj⟩, ?_⟩
    exact freePresheafAugmentedCech_evaluated_exactAt R X U V hU
      (W ⊓ U j) j inf_le_right n
  · refine ⟨W, le_rfl, hx, ?_⟩
    have hz := freePresheafAugmentedCech_isZero_outside R X U V hU W
      (fun h => hxV (h hx)) n
    exact ShortComplex.exact_of_isZero_X₂ _ hz


/--
概要：自由層関手で評価した実際の増大 Čech 鎖複体。
方針：前層の増大 Čech を単体対象の段階で層化してから増大鎖複体を取る。
規約：正次数の尾部は自由層の形式的 Čech 複体となる。
使われ方：TT §3・§8、Toën §3.2 の Ext の計算。
-/
def relativeFreeFormalSheafAugmentedCechComplex :
    ChainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ :=
  augmentedAlternatingFaceComplex
    (((SimplicialObject.Augmented.whiskering _ _).obj (presheafToSheaf _ _)).obj
      (freePresheafCechAugmented R X U V hU))

/--
概要：自由層関手で評価した増大 Čech は全次数で完全。
方針：層化した増大 Čech の既証の完全性を増大関手比較で移す。
規約：被覆の有限性を要求しない。
使われ方：TT §3・§8、Toën §3.2 の Ext 次元移動。
-/
lemma relativeFreeFormalSheafAugmentedCech_acyclic (hcover : (⨆ i, U i) = V) :
    (relativeFreeFormalSheafAugmentedCechComplex R X U V hU).Acyclic := by
  intro n
  exact (exactAt_iff_of_quasiIsoAt
    (augmentedAlternatingFaceMapIso (presheafToSheaf _ _)
      (freePresheafCechAugmented R X U V hU)).hom n).mp
    (relativeFreeSheafAugmentedCech_acyclic R X U V hU hcover n)

/--
概要：切断の Čech の正次数の完全性は増大自由 Čech の Hom の正次数の完全性を与える。
方針：最初の段階では余核の普遍性、残りでは実際の Čech との Hom 比較を使う。
規約：標的層の injectivity を仮定しない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の Cartan 型判定。
-/
lemma relativeFreeFormalSheafAugmentedCech_homExact
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (hcover : (⨆ i, U i) = V)
    (hF : ∀ n : ℕ, ((cechComplexFunctor U).obj
      (F.obj ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).ExactAt (n + 1)) :
    chainHomPositiveExact (relativeFreeFormalSheafAugmentedCechComplex R X U V hU) F := by
  intro n
  cases n with
  | zero =>
    exact resolution_zeroHom_factor _ (relativeFreeFormalSheafAugmentedCech_acyclic R X U V hU hcover)
  | succ n =>
    have he := (exactAt_iff_of_quasiIsoAt (freeSheafCechHomIso R X U F).hom (n + 1)).mpr
      (hF n)
    have hf := (chainHom_exactAt_iff (freeFormalSheafCechComplex R X U) F n).mp he
    change ∀ f : (freeFormalSheafCechComplex R X U).X (n + 1) ⟶ F,
      (freeFormalSheafCechComplex R X U).d (n + 2) (n + 1) ≫ f = 0 →
        ∃ g : (freeFormalSheafCechComplex R X U).X n ⟶ F,
          (freeFormalSheafCechComplex R X U).d (n + 1) n ≫ g = f
    exact hf

/--
概要：Čech 完全性と低次数 Ext 消滅から被覆への Ext 制限は単射。
方針：全次数で完全な自由 Čech 分解に一般の有限次元移動の判定を適用する。
規約：消滅の仮定は n+1 未満だけであり、結論の次数を仮定しない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 のアフィン消滅の帰納。
-/
lemma relativeCech_ext_precomp_injective
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))]
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (n : ℕ)
    (hcover : (⨆ i, U i) = V)
    (hF : ∀ m : ℕ, ((cechComplexFunctor U).obj
      (F.obj ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).ExactAt (m + 1))
    (hvan : ∀ i q : ℕ, 0 < q → q < n + 1 →
      Subsingleton (Ext ((relativeFreeFormalSheafAugmentedCechComplex R X U V hU).X (i + 1)) F q)) :
    Function.Injective
      ((Ext.mk₀ ((relativeFreeFormalSheafAugmentedCechComplex R X U V hU).d 1 0)).precomp F
        (zero_add (n + 1))) :=
  resolution_ext_precomp_injective n _ F
    (relativeFreeFormalSheafAugmentedCech_acyclic R X U V hU hcover)
    (relativeFreeFormalSheafAugmentedCech_homExact R X U V hU F hcover hF) hvan


end SerrePositivity.KST.DerivedGeometry
