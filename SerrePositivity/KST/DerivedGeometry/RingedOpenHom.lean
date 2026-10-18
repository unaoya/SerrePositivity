module

public import SerrePositivity.KST.DerivedGeometry.RingedFreeYoneda
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
概要：環層上の自由 Yoneda 加群の Hom と切断の加法性・自然性。
方針：前層の標準生成元で評価し、加群層化の随伴の両側の自然性を使う。
規約：非可換環層の左加群を扱い、平坦性を要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の実際の係数 Ext の局所消滅。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable (X : TopCat.{u}) (B : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- 概要：環層上の加群層化は加法的。方針：忠実な基礎層への忘却で判定する。
規約：平坦性は不要。使われ方：TT §3、Toën §3.2 の Hom の加法的随伴。 -/
instance ringedModuleSheafification_additive :
    (PresheafOfModules.sheafification.{u} (𝟙 B.obj)).Additive := by
  let L := PresheafOfModules.sheafification.{u} (𝟙 B.obj)
  let F := SheafOfModules.toSheaf.{u} B
  have : (L ⋙ F).Additive := inferInstanceAs
    (PresheafOfModules.toPresheaf B.obj ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive
  exact Functor.additive_of_comp_faithful L F

/--
概要：自由 Yoneda 加群前層からの Hom と切断は加法的に同値。
方針：元の自由 Yoneda の同値の標準生成元上の評価から加法性を得る。
規約：切断はその開の係数環上の元。
使われ方：TT §3、Toën §3.2 の環層係数の Hom 複体。
-/
def ringedFreePresheafHomAddEquiv (U : Opens X) (M : PresheafOfModules.{u} B.obj) :
    ((ringedFreePresheafOnOpen X B).obj U ⟶ M) ≃+ M.obj (.op U) where
  toEquiv := PresheafOfModules.freeYonedaEquiv
  map_add' f g := by rfl

/--
概要：自由 Yoneda 加群層からの Hom と切断は加法的に同値。
方針：加群層化の加法的随伴と前層の加法的同値を合成する。
規約：元の Hom 同値と同じ写像を持つ。
使われ方：TT §3・§8、Toën §3.2 の cocycle と境界の対応。
-/
def ringedFreeSheafHomAddEquiv (U : Opens X) (F : SheafOfModules.{u} B) :
    ((ringedFreeSheafOnOpen X B).obj U ⟶ F) ≃+ F.val.obj (.op U) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).homAddEquiv _ F).trans
    (ringedFreePresheafHomAddEquiv X B U _)

/--
概要：自由加群層の Hom 表示は標的の射と可換。
方針：加群層化の随伴の右自然性を自由 Yoneda の評価へ移す。
規約：標的の射の実際の開上の成分を使う。
使われ方：TT §3、Toën §3.2 の実際の係数分解の微分比較。
-/
lemma ringedFreeSheafHomEquiv_postcomp (U : Opens X) {F G : SheafOfModules.{u} B}
    (f : (ringedFreeSheafOnOpen X B).obj U ⟶ F) (g : F ⟶ G) :
    ringedFreeSheafOnOpenHomEquiv X B U G (f ≫ g) =
      g.val.app (.op U) (ringedFreeSheafOnOpenHomEquiv X B U F f) := by
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)
  exact congrArg PresheafOfModules.freeYonedaEquiv (A.homEquiv_naturality_right f g)

/--
概要：自由加群層の零射は零切断へ対応する。
方針：同じ写像を持つ加法的同値の零の保存を使う。
規約：元の Hom 同値の表記で述べる。
使われ方：TT §3、Toën §3.2 の Ext の cocycle の零微分。
-/
lemma ringedFreeSheafHomEquiv_zero (U : Opens X) (F : SheafOfModules.{u} B) :
    ringedFreeSheafOnOpenHomEquiv X B U F 0 = 0 :=
  (ringedFreeSheafHomAddEquiv X B U F).map_zero

/--
概要：自由 Yoneda 前層の Hom 表示は開の包含と可換。
方針：前層の射の自然性を恒等射の自由生成元で評価する。
規約：係数環の制限に沿う半線形写像をそのまま使う。
使われ方：TT §3・§8、Toën §3.2 の係数 Ext の開制限。
-/
lemma ringedFreePresheafHomEquiv_naturality {V U : Opens X} (f : V ⟶ U)
    (M : PresheafOfModules.{u} B.obj)
    (g : (ringedFreePresheafOnOpen X B).obj U ⟶ M) :
    PresheafOfModules.freeYonedaEquiv ((ringedFreePresheafOnOpen X B).map f ≫ g) =
      M.map f.op (PresheafOfModules.freeYonedaEquiv g) := by
  change g.app (.op V) ((ModuleCat.free (B.obj.obj (.op V))).map
    (↾fun h : V ⟶ V => h ≫ f) (ModuleCat.freeMk (𝟙 V))) =
      M.map f.op (g.app (.op U) (ModuleCat.freeMk (𝟙 U)))
  rw [ModuleCat.free_map_apply]
  have h := PresheafOfModules.naturality_apply g f.op (ModuleCat.freeMk (𝟙 U))
  simpa [ringedFreePresheafOnOpen, PresheafOfModules.free, PresheafOfModules.freeObj] using h

/--
概要：自由加群層の Hom 表示は開の包含と可換。
方針：層化の随伴の左自然性と前層の自由 Yoneda の自然性を合成する。
規約：制限は元の係数加群層の実際の制限写像。
使われ方：TT §3・§8、Toën §3.2 の Ext の有限基本開上での局所消滅。
-/
lemma ringedFreeSheafHomEquiv_naturality {V U : Opens X} (f : V ⟶ U)
    (F : SheafOfModules.{u} B) (g : (ringedFreeSheafOnOpen X B).obj U ⟶ F) :
    ringedFreeSheafOnOpenHomEquiv X B V F ((ringedFreeSheafOnOpen X B).map f ≫ g) =
      F.val.map f.op (ringedFreeSheafOnOpenHomEquiv X B U F g) := by
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)
  have h := A.homEquiv_naturality_left ((ringedFreePresheafOnOpen X B).map f) g
  exact (congrArg PresheafOfModules.freeYonedaEquiv h).trans
    (ringedFreePresheafHomEquiv_naturality X B f _ ((A.homEquiv _ F) g))

end SerrePositivity.KST.DerivedGeometry
