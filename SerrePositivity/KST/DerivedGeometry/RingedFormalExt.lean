module

public import SerrePositivity.KST.DerivedGeometry.RingedCechExt
public import SerrePositivity.KST.DerivedGeometry.FiniteCoproductExt
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
概要：自由層の形式的有限余積の Ext の計算と増大への制限。
方針：層化による余積の保存と Ext の有限余積比較を使う。
規約：形式的余積を実際の自由層の余積へ同型で比較する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の Čech による Ext 消滅。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace Abelian
namespace SerrePositivity.KST.DerivedGeometry
variable (X : TopCat.{u}) (B : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/--
概要：一点の形式的余積から作る自由層は元の開上の自由層と同型。
方針：形式的余積の一元余積の標準同型を層化する。
規約：増大の第0項との実際の比較。
使われ方：TT §3、Toën §3.2 の Ext の始域の移送。
-/
def ringedFormalSheafInclIso (V : Opens X) :
    (ringedFreeFormalSheafFunctor X B).obj ((FormalCoproduct.incl (Opens X)).obj V) ≅
      (ringedFreeSheafOnOpen X B).obj V :=
  (PresheafOfModules.sheafification (𝟙 B.obj)).mapIso
    (((FormalCoproduct.evalCompInclIsoId _ _).app (ringedFreePresheafOnOpen X B)).app V)

/--
概要：一元余積への射は各成分で元の自由層の包含へ一致する。
方針：余積の挿入と desc の公式を層化関手へ移す。
規約：増大先との一元余積の比較を合成して述べる。
使われ方：TT §3・§8、Toën §3.2 の Čech 増大に沿う Ext の計算。
-/
lemma ringedFormalSheafInclIso_component (S : FormalCoproduct.{u} (Opens X)) (V : Opens X)
    (f : S ⟶ (FormalCoproduct.incl (Opens X)).obj V) (i : S.I) :
    (PresheafOfModules.sheafification (𝟙 B.obj)).map
        (Sigma.ι (fun j : S.I => (ringedFreePresheafOnOpen X B).obj (S.obj j)) i) ≫
      (ringedFreeFormalSheafFunctor X B).map f ≫ (ringedFormalSheafInclIso X B V).hom =
        (ringedFreeSheafOnOpen X B).map (f.φ i) := by
  change (PresheafOfModules.sheafification (𝟙 B.obj)).map _ ≫
    (PresheafOfModules.sheafification (𝟙 B.obj)).map _ ≫ (PresheafOfModules.sheafification (𝟙 B.obj)).map _ =
      (PresheafOfModules.sheafification (𝟙 B.obj)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  let P := ringedFreePresheafOnOpen X B
  change Sigma.ι (fun j : S.I => P.obj (S.obj j)) i ≫
    (Sigma.desc fun j : S.I => P.map (f.φ j) ≫
      Sigma.ι (fun _ : PUnit => P.obj V) (f.f j)) ≫
        (Sigma.desc fun _ : PUnit => 𝟙 (P.obj V)) = P.map (f.φ i)
  rw [← Category.assoc, Sigma.ι_comp_desc, Category.assoc, Sigma.ι_comp_desc]
  exact Category.comp_id _

/--
概要：形式的有限余積の各開からの Ext が零なら自由層で評価した余積からの Ext も零。
方針：層化の余積比較同型で実際の有限余積へ移し、Ext の有限余積消滅を使う。
規約：層化が余積を保つことは既存の随伴から得る。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の Čech 分解の低次数消滅。
-/
lemma ringedFormalSheaf_ext_subsingleton (S : FormalCoproduct.{u} (Opens X)) [Finite S.I]
    (F : SheafOfModules.{u} B) (n : ℕ)
    (h : ∀ i, Subsingleton (Ext ((ringedFreeSheafOnOpen X B).obj (S.obj i)) F n)) :
    Subsingleton (Ext ((ringedFreeFormalSheafFunctor X B).obj S) F n) := by
  classical
  letI : Fintype S.I := Fintype.ofFinite S.I
  let L : PresheafOfModules.{u} B.obj ⥤ SheafOfModules.{u} B := PresheafOfModules.sheafification (𝟙 B.obj)
  let D := fun i : S.I => (ringedFreePresheafOnOpen X B).obj (S.obj i)
  letI : HasCoproduct (fun i => L.obj (D i)) :=
    HasColimit.mk ⟨_, isColimitOfHasCoproductOfPreservesColimit L D⟩
  letI : HasBiproduct (fun i => L.obj (D i)) := HasBiproduct.of_hasCoproduct _
  apply ext_subsingleton_of_iso (asIso (sigmaComparison L D)).symm F n
  exact finiteCoproduct_ext_subsingleton (fun i => L.obj (D i)) F n h

/--
概要：形式的有限余積からの Ext の類は層化した各挿入で零を判定できる。
方針：層化の余積比較へ前合成し、有限余積での Ext の零判定を適用する。
規約：射の実際の余積挿入を使う。
使われ方：TT §3・§8、Toën §3.2 の増大 Čech の最初の制限。
-/
lemma ringedFormalSheaf_ext_eq_zero (S : FormalCoproduct.{u} (Opens X)) [Finite S.I]
    (F : SheafOfModules.{u} B) (n : ℕ)
    (α : Ext ((ringedFreeFormalSheafFunctor X B).obj S) F n)
    (h : ∀ i, (Ext.mk₀ ((PresheafOfModules.sheafification (𝟙 B.obj)).map
      (Sigma.ι (fun j : S.I => (ringedFreePresheafOnOpen X B).obj (S.obj j)) i))).comp α
        (zero_add n) = 0) : α = 0 := by
  classical
  letI : Fintype S.I := Fintype.ofFinite S.I
  let L : PresheafOfModules.{u} B.obj ⥤ SheafOfModules.{u} B := PresheafOfModules.sheafification (𝟙 B.obj)
  let D := fun i : S.I => (ringedFreePresheafOnOpen X B).obj (S.obj i)
  letI : HasCoproduct (fun i => L.obj (D i)) :=
    HasColimit.mk ⟨_, isColimitOfHasCoproductOfPreservesColimit L D⟩
  letI : HasBiproduct (fun i => L.obj (D i)) := HasBiproduct.of_hasCoproduct _
  let e := asIso (sigmaComparison L D)
  let eExt := ((evaluation _ AddCommGrpCat.{u}).obj F).mapIso ((extFunctor n).mapIso e.op)
  apply (ConcreteCategory.bijective_of_isIso eExt.hom).injective
  change (Ext.mk₀ e.hom).comp α (zero_add n) =
    (Ext.mk₀ e.hom).comp 0 (zero_add n)
  have hz : (Ext.mk₀ e.hom).comp α (zero_add n) = 0 := by
    apply finiteCoproduct_ext_eq_zero _ F n
    intro i
    rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
    exact (congrArg (fun k => (Ext.mk₀ k).comp α (zero_add n))
      (ι_comp_sigmaComparison L D i)).trans (h i)
  rw [Ext.comp_zero]
  exact hz

/--
概要：一元余積への射に沿う Ext の制限は各成分の制限が零なら零。
方針：各挿入への前合成に Ext の結合則と一元余積の成分比較を適用する。
規約：元の開への制限と増大第0項との比較を含む。
使われ方：TT §3・§8、Toën §3.2 の Čech 増大に沿う消滅。
-/
lemma ringedFormalSheaf_point_precomp_eq_zero
    (S : FormalCoproduct.{u} (Opens X)) [Finite S.I] (V : Opens X)
    (f : S ⟶ (FormalCoproduct.incl (Opens X)).obj V)
    (F : SheafOfModules.{u} B) (n : ℕ)
    (α : Ext ((ringedFreeSheafOnOpen X B).obj V) F n)
    (h : ∀ i, (Ext.mk₀ ((ringedFreeSheafOnOpen X B).map (f.φ i))).comp α
      (zero_add n) = 0) :
    (Ext.mk₀ ((ringedFreeFormalSheafFunctor X B).map f)).comp
      ((Ext.mk₀ (ringedFormalSheafInclIso X B V).hom).comp α (zero_add n)) (zero_add n) = 0 := by
  apply ringedFormalSheaf_ext_eq_zero X B S F n
  intro i
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  exact (congrArg (fun k => (Ext.mk₀ k).comp α (zero_add n))
    (ringedFormalSheafInclIso_component X B S V f i)).trans (h i)

end SerrePositivity.KST.DerivedGeometry
