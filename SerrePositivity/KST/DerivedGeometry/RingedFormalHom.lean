module

public import SerrePositivity.KST.DerivedGeometry.RingedOpenHom
public import SerrePositivity.KST.DerivedGeometry.CoproductHomAddEquiv
public import SerrePositivity.KST.DerivedGeometry.AdditiveProductIso
public import SerrePositivity.KST.DerivedGeometry.AlternatingHomComparison

/-!
概要：環層係数の形式的自由層の Hom と実際の切断の積の自然比較。
方針：加群層化の加法的随伴・余積の Hom・自由 Yoneda の表示を合成する。
規約：基礎アーベル群の自然同型として全ての包含と Čech 面に両立させる。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数 Čech の Hom 比較。
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
概要：開の形式的余積を環層上の自由加群層で評価する関手。
方針：自由 Yoneda 加群前層の余積を取り、元の環層上で層化する。
規約：全ての対象は実際の B 加群層。
使われ方：TT §3、Toën §3.2 の係数自由 Čech。
-/
def ringedFreeFormalSheafFunctor : FormalCoproduct.{u} (Opens X) ⥤ SheafOfModules.{u} B :=
  (FormalCoproduct.eval (Opens X) (PresheafOfModules.{u} B.obj)).obj
    (ringedFreePresheafOnOpen X B) ⋙ PresheafOfModules.sheafification (𝟙 B.obj)

/--
概要：形式的自由層からの Hom と各開の切断の族は加法的に同値。
方針：層化の随伴と余積の Hom の同値を自由 Yoneda の表示へつなぐ。
規約：非可換環層について加法群として比較する。
使われ方：TT §3・§8、Toën §3.2 の Hom 余鎖複体。
-/
def ringedFormalSheafHomAddEquiv (Z : FormalCoproduct.{u} (Opens X))
    (F : SheafOfModules.{u} B) :
    ((ringedFreeFormalSheafFunctor X B).obj Z ⟶ F) ≃+
      (∀ i : Z.I, F.val.obj (.op (Z.obj i))) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).homAddEquiv _ F).trans
    ((coproductHomAddEquiv
      (fun i : Z.I => (ringedFreePresheafOnOpen X B).obj (Z.obj i)) _).trans
        (AddEquiv.piCongrRight (fun i => ringedFreePresheafHomAddEquiv X B (Z.obj i) _)))

/--
概要：形式的自由層の Hom 表示は形式的余積の射と可換。
方針：随伴の左自然性と余積挿入公式を自由 Yoneda の開に関する自然性へ移す。
規約：全ての添字写像と包含を扱う。
使われ方：TT §3・§8、Toën §3.2 の係数 Čech の面と微分。
-/
lemma ringedFormalSheafHomAddEquiv_naturality
    {Z Z' : FormalCoproduct.{u} (Opens X)} (f : Z ⟶ Z')
    (F : SheafOfModules.{u} B) (g : (ringedFreeFormalSheafFunctor X B).obj Z' ⟶ F) (i : Z.I) :
    ringedFormalSheafHomAddEquiv X B Z F ((ringedFreeFormalSheafFunctor X B).map f ≫ g) i =
      F.val.map (f.φ i).op (ringedFormalSheafHomAddEquiv X B Z' F g (f.f i)) := by
  let P := ringedFreePresheafOnOpen X B
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)
  let E := (FormalCoproduct.eval (Opens X) (PresheafOfModules.{u} B.obj)).obj P
  let g' := (A.homEquiv _ F) g
  have h₁ := A.homEquiv_naturality_left (E.map f) g
  have h₂ : Sigma.ι (fun i : Z.I => P.obj (Z.obj i)) i ≫ E.map f ≫ g' =
      P.map (f.φ i) ≫ Sigma.ι (P.obj ∘ Z'.obj) (f.f i) ≫ g' := by
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ g')
      (Sigma.ι_comp_desc (fun j : Z.I => P.map (f.φ j) ≫
        Sigma.ι (P.obj ∘ Z'.obj) (f.f j)) i)).trans ?_
    exact Category.assoc _ _ _
  exact (congrArg (fun k => PresheafOfModules.freeYonedaEquiv
      (Sigma.ι (fun i : Z.I => P.obj (Z.obj i)) i ≫ k)) h₁).trans
    ((congrArg PresheafOfModules.freeYonedaEquiv h₂).trans
      (ringedFreePresheafHomEquiv_naturality X B (f.φ i) _
        (Sigma.ι (P.obj ∘ Z'.obj) (f.f i) ≫ g')))

/--
概要：形式的自由層の Hom の加法群と切断の圏論的な積の同型。
方針：加法的 Hom 表示と関数加法群と選ばれた積の比較を合成する。
規約：元の切断の加法群の積を使う。
使われ方：TT §3、Toën §3.2 の係数 Čech の各項。
-/
def ringedFormalSheafHomIso (F : SheafOfModules.{u} B) (Z : FormalCoproduct.{u} (Opens X)) :
    (preadditiveYoneda.obj F).obj (.op ((ringedFreeFormalSheafFunctor X B).obj Z)) ≅
      ∏ᶜ (fun i : Z.I => F.val.presheaf.obj (.op (Z.obj i))) :=
  (ringedFormalSheafHomAddEquiv X B Z F).toAddCommGrpIso ≪≫
    (additiveProductIsoPi (fun i : Z.I => F.val.presheaf.obj (.op (Z.obj i)))).symm

/--
概要：Hom 比較の各射影は自由 Yoneda の切断の成分と一致する。
方針：積の標準比較の射影公式を使う。
規約：加法群の実際の射の等式。
使われ方：TT §3、Toën §3.2 の Hom 比較の自然性。
-/
@[reassoc]
lemma ringedFormalSheafHomIso_hom_π (F : SheafOfModules.{u} B)
    (Z : FormalCoproduct.{u} (Opens X)) (i : Z.I) :
    (ringedFormalSheafHomIso X B F Z).hom ≫ Pi.π _ i =
      AddCommGrpCat.ofHom ((Pi.evalAddMonoidHom (fun i : Z.I => F.val.obj (.op (Z.obj i))) i).comp
        (ringedFormalSheafHomAddEquiv X B Z F).toAddMonoidHom) := by
  dsimp only [ringedFormalSheafHomIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, additiveProductIsoPi_inv_π]
  rfl

/--
概要：環層上の形式的自由層の Hom は実際の切断の反変評価と自然同型。
方針：各射影で Hom と切断の自然性を適用する。
規約：Čech の全ての面と退化を含む自然同型。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数 Čech 比較。
-/
def ringedFormalSheafHomNatIso (F : SheafOfModules.{u} B) :
    (ringedFreeFormalSheafFunctor X B).op ⋙ preadditiveYoneda.obj F ≅
      (FormalCoproduct.evalOp (Opens X) AddCommGrpCat.{u}).obj F.val.presheaf :=
  NatIso.ofComponents (fun Z => ringedFormalSheafHomIso X B F Z.unop) (by
    intro Z Z' f
    apply Pi.hom_ext
    intro i
    simp only [Category.assoc, ringedFormalSheafHomIso_hom_π, FormalCoproduct.evalOp,
      Functor.comp_map, Functor.comp_obj, Pi.lift_comp_π, Pi.lift_comp_π_assoc,
      ringedFormalSheafHomIso_hom_π_assoc]
    ext g
    exact ringedFormalSheafHomAddEquiv_naturality X B f.unop F g i)

end SerrePositivity.KST.DerivedGeometry
