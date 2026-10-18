module

public import SerrePositivity.KST.DerivedGeometry.RingedFormalHom
public import SerrePositivity.KST.DerivedGeometry.RingedFreeCechExact
public import SerrePositivity.KST.DerivedGeometry.RingedExtLocalVanishing
public import SerrePositivity.KST.DerivedGeometry.ChainHomExact
public import SerrePositivity.KST.DerivedGeometry.ResolutionExtCriterion

/-!
概要：実際の環層加群層圏の自由 Čech の Hom 比較と Ext 制限単射性。
方針：全次数で完全な自由増大 Čech と切断の Čech の同型へ有限次元移動を適用する。
規約：環層の非可換性・非平坦性を許す。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数アフィン消滅。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace Abelian
namespace SerrePositivity.KST.DerivedGeometry
variable (X : TopCat.{u}) (B : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {ι : Type u} (U : ι → Opens X) (V : Opens X) (hU : ∀ i, U i ≤ V)

/--
概要：形式的自由加群層の Čech の交代面鎖複体。
方針：開の形式的 Čech を実際の環層上の自由層で評価する。
規約：全次数の有限和と符号を保持する。
使われ方：TT §3、Toën §3.2 の係数 Hom の Čech 比較。
-/
def ringedFormalSheafCechComplex : ChainComplex (SheafOfModules.{u} B) ℕ :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj
    ((FormalCoproduct.mk ι U).cech ⋙ ringedFreeFormalSheafFunctor X B)

/--
概要：環層係数の自由 Čech からの Hom 複体と実際の切断 Čech の同型。
方針：交代面の反変比較と自由層の Hom の自然同型を合成する。
規約：固定環に忘れて分解を置き換えない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数 Čech 次元移動。
-/
def ringedSheafCechHomIso (F : SheafOfModules.{u} B) :
    chainHomComplex (ringedFormalSheafCechComplex X B U) F ≅
      (cechComplexFunctor U).obj F.val.presheaf :=
  alternatingFaceContravariantIso (preadditiveYoneda.obj F)
      ((FormalCoproduct.mk ι U).cech ⋙ ringedFreeFormalSheafFunctor X B) ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).mapIso
      (Functor.isoWhiskerLeft (FormalCoproduct.mk ι U).cech.rightOp
        (ringedFormalSheafHomNatIso X B F))

/--
概要：環層係数の自由増大 Čech を単体対象の段階で層化した鎖複体。
方針：実際の加群層化の後で増大交代面複体を取る。
規約：元の層化後の増大 Čech との比較を次に証明する。
使われ方：TT §3、Toën §3.2 の Ext 分解の各項の計算。
-/
def ringedFormalSheafAugmentedCechComplex : ChainComplex (SheafOfModules.{u} B) ℕ :=
  augmentedAlternatingFaceComplex
    (((SimplicialObject.Augmented.whiskering _ _).obj
      (PresheafOfModules.sheafification (𝟙 B.obj))).obj
        (ringedFreePresheafCechAugmented X B U V hU))

/--
概要：単体対象の段階で層化した自由増大 Čech は全次数で完全。
方針：既証の実際の自由分解から増大鎖複体と層化の比較同型で移す。
規約：任意の開の任意の被覆を扱う。
使われ方：TT §3・§8、Toën §3.2 の係数 Ext 制限単射性。
-/
lemma ringedFormalSheafAugmentedCech_acyclic (hcover : (⨆ i, U i) = V) :
    (ringedFormalSheafAugmentedCechComplex X B U V hU).Acyclic := by
  intro n
  exact (exactAt_iff_of_quasiIsoAt
    (augmentedAlternatingFaceMapIso (PresheafOfModules.sheafification (𝟙 B.obj))
      (ringedFreePresheafCechAugmented X B U V hU)).hom n).mp
    (ringedFreeSheafAugmentedCech_acyclic X B U V hU hcover n)

/--
概要：切断 Čech の正次数完全性から自由増大 Čech の Hom の正次数完全性を得る。
方針：最初の段階は余核の普遍性、残りは Čech の Hom 同型による完全性の移送を使う。
規約：標的の injectivity は仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数版 Cartan 型判定。
-/
lemma ringedFormalSheafAugmentedCech_homExact (F : SheafOfModules.{u} B)
    (hcover : (⨆ i, U i) = V)
    (hF : ∀ n : ℕ, ((cechComplexFunctor U).obj F.val.presheaf).ExactAt (n + 1)) :
    chainHomPositiveExact (ringedFormalSheafAugmentedCechComplex X B U V hU) F := by
  intro n
  cases n with
  | zero =>
    exact resolution_zeroHom_factor _ (ringedFormalSheafAugmentedCech_acyclic X B U V hU hcover)
  | succ n =>
    have he := (exactAt_iff_of_quasiIsoAt (ringedSheafCechHomIso X B U F).hom (n + 1)).mpr
      (hF n)
    have hf := (chainHom_exactAt_iff (ringedFormalSheafCechComplex X B U) F n).mp he
    change ∀ f : (ringedFormalSheafCechComplex X B U).X (n + 1) ⟶ F,
      (ringedFormalSheafCechComplex X B U).d (n + 2) (n + 1) ≫ f = 0 →
        ∃ g : (ringedFormalSheafCechComplex X B U).X n ⟶ F,
          (ringedFormalSheafCechComplex X B U).d (n + 1) n ≫ g = f
    exact hf

/--
概要：実際の環層加群層圏で Čech 完全性と低次数 Ext 消滅から被覆への制限は単射。
方針：全次数で完全な増大自由分解へ証明済みの有限次元移動を適用する。
規約：結論の次数の Ext 消滅を仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数アフィン消滅。
-/
lemma ringedCech_ext_precomp_injective (F : SheafOfModules.{u} B) (n : ℕ)
    (hcover : (⨆ i, U i) = V)
    (hF : ∀ m : ℕ, ((cechComplexFunctor U).obj F.val.presheaf).ExactAt (m + 1))
    (hvan : ∀ i q : ℕ, 0 < q → q < n + 1 →
      Subsingleton (Ext ((ringedFormalSheafAugmentedCechComplex X B U V hU).X (i + 1)) F q)) :
    Function.Injective
      ((Ext.mk₀ ((ringedFormalSheafAugmentedCechComplex X B U V hU).d 1 0)).precomp F
        (zero_add (n + 1))) :=
  resolution_ext_precomp_injective n _ F
    (ringedFormalSheafAugmentedCech_acyclic X B U V hU hcover)
    (ringedFormalSheafAugmentedCech_homExact X B U V hU F hcover hF) hvan

end SerrePositivity.KST.DerivedGeometry
