module

public import SerrePositivity.KST.DerivedGeometry.SheafInjectiveSections
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
概要：開上の切断を表す自由加群層。
方針：Yoneda、自由加群、層化の三つの随伴を合成する。
規約：係数環は非可換でもよく、自由層は実際の層化で構成する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の injective と Čech の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable (R : Type u) [Ring R] (X : TopCat.{u})

/--
概要：開の表現可能前層の自由 R 加群前層。
方針：Yoneda に各点で自由加群関手を合成する。
規約：開を動かす関手として束ねる。
使われ方：TT §3、Toën §3.2 の自由 Čech 鎖複体。
-/
def freeModulePresheafOnOpen : Opens X ⥤ ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free R)

/--
概要：開上の切断を表す自由 R 加群層。
方針：自由加群前層を実際に層化する。
規約：被覆元の形式的な記号だけを対象にしない。
使われ方：TT §3・§8、Toën §3.2 の切断の表示。
-/
def freeModuleSheafOnOpen : Opens X ⥤
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) :=
  freeModulePresheafOnOpen R X ⋙ presheafToSheaf _ _

/--
概要：自由加群層からの射は同じ開上の切断と一対一に対応する。
方針：層化・自由加群の随伴と Yoneda の同値を合成する。
規約：実際の Hom 型と切断の型の同値。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の injectivity。
-/
def freeModuleSheafOnOpenHomEquiv (U : Opens X)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    ((freeModuleSheafOnOpen R X).obj U ⟶ F) ≃ F.obj.obj (.op U) :=
  ((sheafificationAdjunction _ _).homEquiv _ F).trans
    ((((ModuleCat.adj R).whiskerRight ((Opens X)ᵒᵖ)).homEquiv _ F.obj).trans yonedaEquiv)

/--
概要：自由加群層の Hom の表示は開の包含と両立する。
方針：二つの随伴の左自然性と Yoneda の自然性を順に適用する。
規約：切断側は元の制限写像。
使われ方：TT §3、Toën §3.2 の injective 層の制限の全射性。
-/
lemma freeModuleSheafOnOpenHomEquiv_naturality {V U : Opens X} (f : V ⟶ U)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (g : (freeModuleSheafOnOpen R X).obj U ⟶ F) :
    freeModuleSheafOnOpenHomEquiv R X V F ((freeModuleSheafOnOpen R X).map f ≫ g) =
      F.obj.map f.op (freeModuleSheafOnOpenHomEquiv R X U F g) := by
  let A := sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat.{u} R)
  let B := (ModuleCat.adj R).whiskerRight ((Opens X)ᵒᵖ)
  have h₁ := A.homEquiv_naturality_left ((freeModulePresheafOnOpen R X).map f) g
  have h₂ := B.homEquiv_naturality_left (yoneda.map f) ((A.homEquiv _ F) g)
  exact (congrArg (fun k => yonedaEquiv ((B.homEquiv _ F.obj) k)) h₁).trans
    ((congrArg yonedaEquiv h₂).trans (yonedaEquiv_naturality _ f).symm)

/--
概要：開の包含から得られる自由加群前層の射は mono。
方針：各成分の自由加群の写像の単射性を、薄い圏の射の一意性から得る。
規約：被覆や有限性の条件は不要。
使われ方：TT §3、Toën §3.2 の自由層の包含。
-/
instance freeModulePresheafOnOpen_map_mono {V U : Opens X} (f : V ⟶ U) :
    Mono ((freeModulePresheafOnOpen R X).map f) := by
  have (W : (Opens X)ᵒᵖ) : Mono (((freeModulePresheafOnOpen R X).map f).app W) := by
    apply (ModuleCat.mono_iff_injective _).mpr
    have : Subsingleton ((yoneda.obj V).obj W) :=
      inferInstanceAs (Subsingleton (W.unop ⟶ V))
    exact Finsupp.mapDomain_injective (fun _ _ _ => Subsingleton.elim _ _)
  exact NatTrans.mono_of_mono_app _

/--
概要：開の包含から得られる自由加群層の射は mono。
方針：自由前層の mono に層化の左完全性を適用する。
規約：層化後の実際の射についての主張。
使われ方：TT §3・§8、Toën §3.2 の injectivity の適用。
-/
instance freeModuleSheafOnOpen_map_mono {V U : Opens X} (f : V ⟶ U) :
    Mono ((freeModuleSheafOnOpen R X).map f) := by
  change Mono ((presheafToSheaf _ _).map ((freeModulePresheafOnOpen R X).map f))
  infer_instance

/--
概要：injective 加群層の全ての開制限は切断上で全射。
方針：自由層の mono に対して射を延長し、切断の Hom 表示の自然性を使う。
規約：injective の存在を新たな仮定にせず、任意の injective 対象について述べる。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の Čech 非輪状性。
-/
lemma injectiveModuleSheaf_restriction_surjective
    (I : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) [Injective I]
    {V U : Opens X} (f : V ⟶ U) : Function.Surjective (I.obj.map f.op) := by
  intro s
  let g := (freeModuleSheafOnOpenHomEquiv R X V I).symm s
  let h := Injective.factorThru g ((freeModuleSheafOnOpen R X).map f)
  refine ⟨freeModuleSheafOnOpenHomEquiv R X U I h, ?_⟩
  rw [← freeModuleSheafOnOpenHomEquiv_naturality, Injective.comp_factorThru]
  exact (freeModuleSheafOnOpenHomEquiv R X V I).apply_symm_apply s

end SerrePositivity.KST.DerivedGeometry
