module

public import SerrePositivity.KST.DerivedGeometry.ResolutionExtCriterion
public import SerrePositivity.KST.DerivedGeometry.ChainHomExact
public import SerrePositivity.KST.DerivedGeometry.InjectiveCechExact

/-!
概要：実際の切断の Čech の完全性から自由層分解に沿う Ext 制限の単射性を導く。
方針：増大自由 Čech の Hom を通常の Čech と比較し、有限次元移動を適用する。
規約：係数環は非可換でもよく、平坦性を要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン導来比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits TopologicalSpace Abelian
namespace SerrePositivity.KST.DerivedGeometry
variable (R : Type u) [Ring R] (X : TopCat.{u}) {ι : Type u} (U : ι → Opens X)

/--
概要：自由層関手で評価した実際の増大 Čech 鎖複体。
方針：前層の増大 Čech を単体対象の段階で層化してから増大鎖複体を取る。
規約：正次数の尾部は自由層の形式的 Čech 複体となる。
使われ方：TT §3・§8、Toën §3.2 の Ext の計算。
-/
def freeFormalSheafAugmentedCechComplex :
    ChainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ :=
  augmentedAlternatingFaceComplex
    (((SimplicialObject.Augmented.whiskering _ _).obj (presheafToSheaf _ _)).obj
      (freePresheafCechAugmented R X U ⊤ (fun _ => le_top)))

/--
概要：自由層関手で評価した増大 Čech は全次数で完全。
方針：層化した増大 Čech の既証の完全性を増大関手比較で移す。
規約：被覆の有限性を要求しない。
使われ方：TT §3・§8、Toën §3.2 の Ext 次元移動。
-/
lemma freeFormalSheafAugmentedCech_acyclic (hcover : (⨆ i, U i) = ⊤) :
    (freeFormalSheafAugmentedCechComplex R X U).Acyclic := by
  intro n
  exact (exactAt_iff_of_quasiIsoAt
    (augmentedAlternatingFaceMapIso (presheafToSheaf _ _)
      (freePresheafCechAugmented R X U ⊤ (fun _ => le_top))).hom n).mp
    (freeSheafAugmentedCech_acyclic R X U ⊤ (fun _ => le_top) hcover n)

/--
概要：切断の Čech の正次数の完全性は増大自由 Čech の Hom の正次数の完全性を与える。
方針：最初の段階では余核の普遍性、残りでは実際の Čech との Hom 比較を使う。
規約：標的層の injectivity を仮定しない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の Cartan 型判定。
-/
lemma freeFormalSheafAugmentedCech_homExact
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (hcover : (⨆ i, U i) = ⊤)
    (hF : ∀ n : ℕ, ((cechComplexFunctor U).obj
      (F.obj ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).ExactAt (n + 1)) :
    chainHomPositiveExact (freeFormalSheafAugmentedCechComplex R X U) F := by
  intro n
  cases n with
  | zero =>
    exact resolution_zeroHom_factor _ (freeFormalSheafAugmentedCech_acyclic R X U hcover)
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
lemma cech_ext_precomp_injective
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))]
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (n : ℕ)
    (hcover : (⨆ i, U i) = ⊤)
    (hF : ∀ m : ℕ, ((cechComplexFunctor U).obj
      (F.obj ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).ExactAt (m + 1))
    (hvan : ∀ i q : ℕ, 0 < q → q < n + 1 →
      Subsingleton (Ext ((freeFormalSheafAugmentedCechComplex R X U).X (i + 1)) F q)) :
    Function.Injective
      ((Ext.mk₀ ((freeFormalSheafAugmentedCechComplex R X U).d 1 0)).precomp F
        (zero_add (n + 1))) :=
  resolution_ext_precomp_injective n _ F
    (freeFormalSheafAugmentedCech_acyclic R X U hcover)
    (freeFormalSheafAugmentedCech_homExact R X U F hcover hF) hvan

end SerrePositivity.KST.DerivedGeometry
