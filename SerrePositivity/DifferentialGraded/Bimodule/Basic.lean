module

public import SerrePositivity.DifferentialGraded.Module.LeftAction
public import SerrePositivity.DifferentialGraded.Module.HomElements
public import SerrePositivity.DifferentialGraded.Module.Category
public import SerrePositivity.DifferentialGraded.Module.YonedaFunctor
public import SerrePositivity.DifferentialGraded.Module.LeftRepresentable
public import SerrePositivity.DifferentialGraded.Module.LeftCategory
public import SerrePositivity.DifferentialGraded.Module.Action
public import SerrePositivity.DifferentialGraded.Module.HomWhisker
public import SerrePositivity.DifferentialGraded.Module.HomIsoSquare
public import SerrePositivity.DifferentialGraded.Module.HomSquareComposition

/-!
# Bimodule.Basic

## 概要
15 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## Basic（旧 SerrePositivity/DifferentialGraded/Bimodule/Basic.lean） -/

/-! # 右B・左C dg bimodule

Cから右B加群の全Hom end豊穣圏へのdg関手を使う。
左C作用は最初から全dg自然な右B加群間のHomに値を持ち、閉零自然性では代用しない。
積dg圏とのuncurrying比較は後続の工程。
-/

@[expose] public section Basic
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 右B・左Cの全dg自然なbimodule。 -/
def Bimodule := DGFunctor A C (RightModule A B)

namespace Bimodule
variable {A B C}

/-- 右B加群への豊穣関手として読む。 -/
abbrev toFunctor (M : Bimodule A B C) : DGFunctor A C (RightModule A B) := M

/-- Cの対象を固定した右B加群。 -/
abbrev rightAt (M : Bimodule A B C) (c : C) : RightModule A B := M.toFunctor.obj c

/-- Bの対象を固定した左C加群。 -/
def leftAt (M : Bimodule A B C) (b : B) : LeftModule A C :=
  M.toFunctor.comp (moduleEvaluationDG A B b)

/-- 両対象での値。 -/
abbrev value (M : Bimodule A B C) (b : B) (c : C) : Complex A :=
  (M.rightAt c).obj (op b)

/-- 左C作用の全次数cochain。 -/
def leftCochain (M : Bimodule A B C) {c c' : C} {q : ℤ}
    (g : GradedHom A c c' q) (b : B) :
    Cochain (M.value b c) (M.value b c') q :=
  (moduleHomπ A B (M.rightAt c) (M.rightAt c') b).f q ((M.toFunctor.map c c').f q g)

/-- 二つの作用の交換は全Hom endの自然性そのもの。 -/
lemma interchange (M : Bimodule A B C) {b b' : B} {c c' : C} {p q : ℤ}
    (f : GradedHom A (op b') (op b) p) (g : GradedHom A c c' q) :
    (((M.rightAt c).map (op b') (op b)).f p f).comp (M.leftCochain g b)
        (by omega : p + q = q + p) =
      (q * p).negOnePow • ((M.leftCochain g b').comp
        (((M.rightAt c').map (op b') (op b)).f p f) rfl) :=
  moduleHomElement_naturality A B q ((M.toFunctor.map c c').f q g) (op b') (op b) p f

/-- 左cochainは評価によって得た左加群の作用と一致する。 -/
lemma leftCochain_eq (M : Bimodule A B C) {c c' : C} {q : ℤ}
    (g : GradedHom A c c' q) (b : B) :
    M.leftCochain g b = ((M.leftAt b).map c c').f q g := rfl

end Bimodule
end SerrePositivity.DifferentialGraded
end

end Basic

/-! ## Ext（旧 SerrePositivity/DifferentialGraded/Bimodule/Ext.lean） -/

/-! # bimoduleの二つの作用による外延性 -/

@[expose] public section Ext
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 両因子での制限が一致すれば、主Hom endを持つbimoduleも一致する。 -/
lemma ext_rightAt_leftAt (M N : Bimodule A B C)
    (hr : ∀ c, M.rightAt c = N.rightAt c) (hl : ∀ b, M.leftAt b = N.leftAt b) : M = N := by
  rcases M with ⟨Mo, Mm, Mi, Mc⟩
  rcases N with ⟨No, Nm, Ni, Nc⟩
  have ho : Mo = No := funext hr
  subst No
  apply EnrichedFunctor.ext (Complex A) (C := C) (D := RightModule A B)
    (F := ⟨Mo, Mm, Mi, Mc⟩) (G := ⟨Mo, Nm, Ni, Nc⟩) (fun _ => rfl)
  intro c d
  rw [eqToHom_refl, Category.comp_id]
  apply moduleHom_ext
  intro b
  have hmap (F G : LeftModule A C) (h : F = G) : HEq (F.map c d) (G.map c d) := by
    cases h
    rfl
  exact eq_of_heq (hmap _ _ (hl b))

end SerrePositivity.DifferentialGraded.Bimodule
end

end Ext

/-! ## Action（旧 SerrePositivity/DifferentialGraded/Bimodule/Action.lean） -/

/-! # bimoduleの斉次二作用とKoszul交換則 -/

@[expose] public section Action
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory Opposite CochainComplex HomComplex
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 右B作用。 -/
def actRight (M : Bimodule A B C) {b b' : B} {c : C} {p r n : ℤ}
    (f : GradedHom A (op b') (op b) p) (v : (M.value b' c).X r)
    (hn : r + p = n) : (M.value b c).X n :=
  moduleAction A (M.rightAt c) f v hn

/-- 左C作用。 -/
def actLeft (M : Bimodule A B C) {b : B} {c c' : C} {q r n : ℤ}
    (g : GradedHom A c c' q) (v : (M.value b c).X r)
    (hn : r + q = n) : (M.value b c').X n :=
  (M.leftCochain g b).v r n hn v

/-- 左右の作用を交換すると次数積のKoszul符号を得る。 -/
lemma act_interchange (M : Bimodule A B C) {b b' : B} {c c' : C} {p q r n : ℤ}
    (f : GradedHom A (op b') (op b) p) (g : GradedHom A c c' q)
    (v : (M.value b' c).X r) (hn : r + (q + p) = n) :
    M.actLeft (n := n) g (M.actRight f v rfl) (by omega) =
      (q * p).negOnePow • M.actRight (n := n) f (M.actLeft g v rfl) (by omega) := by
  have h := congrArg (fun h => h.v r n hn v) (M.interchange f g)
  rw [Cochain.comp_v _ _ (by omega) r (r + p) n rfl (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ rfl r (r + q) n rfl (by omega)] at h
  exact h

lemma actRight_unit (M : Bimodule A B C) (b : B) (c : C) (r : ℤ)
    (v : (M.value b c).X r) :
    M.actRight (unitElement A (op b)).val v (add_zero r) = v :=
  moduleAction_unit A (M.rightAt c) (op b) r v

lemma actLeft_unit (M : Bimodule A B C) (b : B) (c : C) (r : ℤ)
    (v : (M.value b c).X r) :
    M.actLeft (unitElement A c).val v (add_zero r) = v := by
  change leftAction A (M.leftAt b) (unitElement A c).val v (add_zero r) = v
  exact leftAction_unit A (M.leftAt b) c r v

end SerrePositivity.DifferentialGraded.Bimodule
end

end Action

/-! ## ActionEvaluation（旧 SerrePositivity/DifferentialGraded/Bimodule/ActionEvaluation.lean） -/

/-! # bimoduleの左cochainと左加群作用の成分比較 -/

@[expose] public section ActionEvaluation
universe u v w

namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma leftCochain_apply (M : Bimodule A B C) {c c' : C} {p i n : ℤ}
    (g : GradedHom A c c' p) (b : B) (v : (M.value b c).X i) (hn : i + p = n) :
    (M.leftCochain g b).v i n hn v = leftAction A (M.leftAt b) g v hn := rfl

end SerrePositivity.DifferentialGraded.Bimodule

end ActionEvaluation

/-! ## ActionElement（旧 SerrePositivity/DifferentialGraded/Bimodule/ActionElement.lean） -/

/-! # 値の複体を始域・終域に固定したbimoduleの斉次左作用 -/

@[expose] public section ActionElement
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 左加群への変換を型に含めず、全Hom cochainから左作用を評価する。 -/
@[irreducible]
def leftActionElement (M : Bimodule A B C) {c c' : C} {p i n : ℤ}
    (g : GradedHom A c c' p) (b : B) (v : (M.value b c).X i) (hn : i + p = n) :
    (M.value b c').X n :=
  (M.leftCochain g b).v i n hn v

lemma leftActionElement_eq (M : Bimodule A B C) {c c' : C} {p i n : ℤ}
    (g : GradedHom A c c' p) (b : B) (v : (M.value b c).X i) (hn : i + p = n) :
    leftActionElement A M g b v hn = leftAction A (M.leftAt b) g v hn := by
  unfold leftActionElement
  exact leftCochain_apply A B C M g b v hn

end SerrePositivity.DifferentialGraded.Bimodule
end

end ActionElement

/-! ## Identity（旧 SerrePositivity/DifferentialGraded/Bimodule/Identity.lean） -/

/-! # 対角Homを値とする単位dg bimodule -/

@[expose] public section Identity
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- Hom_D(b,c)を値とする対角bimodule。 -/
def diagonal : Bimodule A D D := dgYoneda A D

lemma diagonal_rightAt (c : D) : (diagonal A D).rightAt c = representable A c := rfl

lemma diagonal_value (b c : D) : (diagonal A D).value b c = (b ⟶[Complex A] c) := rfl

lemma diagonal_leftAt (b : D) : (diagonal A D).leftAt b = leftRepresentable A b := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (diagonal A D).leftAt b) (G := leftRepresentable A b) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Cochain.ext
  intro r n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  change (((moduleHomπ A D (representable A x) (representable A y) b).f p
      ((yonedaHom A D x y).f p f)).v r n hn) h =
    leftAction A (leftRepresentable A b) f h hn
  rw [yonedaHom_element, leftRepresentable_action]

end SerrePositivity.DifferentialGraded.Bimodule
end

end Identity

/-! ## Transpose（旧 SerrePositivity/DifferentialGraded/Bimodule/Transpose.lean） -/

/-! # bimoduleの右作用を左加群の主Hom endへ転置する -/

@[expose] public section Transpose
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 交換則を左C作用の後に右B作用を行う向きへ書き直す。 -/
lemma transposeInterchange (M : Bimodule A B C) {b b' : Bᵒᵖ} {c c' : C} {p q : ℤ}
    (f : GradedHom A b b' p) (g : GradedHom A c c' q) :
    (M.leftCochain g b.unop).comp (((M.rightAt c').map b b').f p f)
      rfl =
    (p * q).negOnePow • ((((M.rightAt c).map b b').f p f).comp
      (M.leftCochain g b'.unop) (by omega)) := by
  have h := congrArg (fun t => (p * q).negOnePow • t) (M.interchange f g)
  rw [mul_comm q p, smul_smul, Int.units_mul_self, one_smul] at h
  simpa only [Opposite.op_unop] using h.symm

variable [Small.{u} C]

/-- 右BのHomをパラメータにした全次数自然な左C加群間の変換。 -/
def transposeParam (M : Bimodule A B C) (b b' : Bᵒᵖ) :
    ModuleParamTrans A Cᵒᵖ (b ⟶[Complex A] b')
      (M.leftAt b.unop).toRightOpposite (M.leftAt b'.unop).toRightOpposite where
  app c := (M.rightAt c.unop.unop).map b b'
  naturality x y := by
    apply moduleParamNaturality_of_apply A
    intro x y p q r n hn f g m
    have h := Cochain.congr_v
      (M.transposeInterchange f (c := x.unop.unop) (c' := y.unop.unop) g) r n (by omega)
    rw [Cochain.comp_v _ _ _ r (r + q) n rfl (by omega), Cochain.units_smul_v,
      Cochain.comp_v _ _ _ r (r + p) n rfl (by omega)] at h
    change (((M.rightAt y.unop.unop).map b b').f p f).v (r + q) n (by omega)
        (((𝟙 _ ≫ (M.leftAt b.unop).map x.unop.unop y.unop.unop).f q g).v r (r + q) rfl m) =
      (p * q).negOnePow •
        (((𝟙 _ ≫ (M.leftAt b'.unop).map x.unop.unop y.unop.unop).f q g).v
          (r + p) n (by omega)
          ((((M.rightAt x.unop.unop).map b b').f p f).v r (r + p) rfl m))
    simp only [Category.id_comp]
    exact congrArg (fun t => t m) h

/-- 右B作用の実際の左加群Hom複体への持ち上げ。 -/
def transposeHom (M : Bimodule A B C) (b b' : Bᵒᵖ) :
    (b ⟶[Complex A] b') ⟶ leftModuleHom A C (M.leftAt b.unop) (M.leftAt b'.unop) :=
  (moduleHomEquiv A Cᵒᵖ _ _ _).symm (M.transposeParam b b')

@[reassoc]
lemma transposeHom_π (M : Bimodule A B C) (b b' : Bᵒᵖ) (c : C) :
    M.transposeHom b b' ≫ moduleHomπ A Cᵒᵖ
      (M.leftAt b.unop).toRightOpposite (M.leftAt b'.unop).toRightOpposite (op c) =
    (M.rightAt c).map b b' :=
  moduleHomEquiv_symm_π A Cᵒᵖ _ _ _ (M.transposeParam b b') (op c)

/-- Bᵒᵖから全Hom endを持つ左C加群圏への実際のdg関手。 -/
def transposeDG (M : Bimodule A B C) : DGFunctor A Bᵒᵖ (LeftModule A C) where
  obj b := M.leftAt b.unop
  map := M.transposeHom
  map_id b := by
    apply moduleHom_ext
    intro c
    change eId (Complex A) b ≫ M.transposeHom b b ≫
      moduleHomπ A Cᵒᵖ (M.leftAt b.unop).toRightOpposite
        (M.leftAt b.unop).toRightOpposite (op c.unop) =
      moduleIdentity A Cᵒᵖ (M.leftAt b.unop).toRightOpposite ≫
        moduleHomπ A Cᵒᵖ (M.leftAt b.unop).toRightOpposite
          (M.leftAt b.unop).toRightOpposite (op c.unop)
    rw [transposeHom_π, moduleIdentity_π]
    change eId (Complex A) b ≫ (M.rightAt c.unop).map b b =
      identity ((M.rightAt c.unop).obj b)
    exact (M.rightAt c.unop).toFunctor.map_id b
  map_comp b b' b'' := by
    apply moduleHom_ext
    intro c
    change eComp (Complex A) b b' b'' ≫ M.transposeHom b b'' ≫
      moduleHomπ A Cᵒᵖ (M.leftAt b.unop).toRightOpposite
        (M.leftAt b''.unop).toRightOpposite (op c.unop) =
      (M.transposeHom b b' ⊗ₘ M.transposeHom b' b'') ≫
        moduleComposition A Cᵒᵖ (M.leftAt b.unop).toRightOpposite
          (M.leftAt b'.unop).toRightOpposite (M.leftAt b''.unop).toRightOpposite ≫
            moduleHomπ A Cᵒᵖ (M.leftAt b.unop).toRightOpposite
              (M.leftAt b''.unop).toRightOpposite (op c.unop)
    rw [transposeHom_π, moduleComposition_π, tensorHom_comp_tensorHom_assoc,
      transposeHom_π, transposeHom_π]
    exact (M.rightAt c.unop).toFunctor.map_comp b b' b''

end SerrePositivity.DifferentialGraded.Bimodule
end

end Transpose

/-! ## OfActions（旧 SerrePositivity/DifferentialGraded/Bimodule/OfActions.lean） -/

/-! # 全次数自然な左作用族からのbimodule構成子 -/

@[expose] public section OfActions
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 左作用の全次数自然性と各評価での単位・合成からbimoduleを構成する。 -/
def ofParamTrans (P : C → RightModule A B)
    (a : ∀ c c' : C, ModuleParamTrans A B (c ⟶[Complex A] c') (P c) (P c'))
    (hi : ∀ (c : C) (b : Bᵒᵖ),
      eId (Complex A) c ≫ (a c c).app b = identity ((P c).obj b))
    (hc : ∀ (c c' c'' : C) (b : Bᵒᵖ),
      eComp (Complex A) c c' c'' ≫ (a c c'').app b =
        ((a c c').app b ⊗ₘ (a c' c'').app b) ≫ enrichedComposition _ _ _) :
    Bimodule A B C where
  obj := P
  map c c' := (moduleHomEquiv A B _ _ _).symm (a c c')
  map_id c := by
    apply moduleHom_ext
    intro b
    rw [Category.assoc, moduleHomEquiv_symm_π]
    exact (hi c (op b)).trans (moduleIdentity_π A B (P c) b).symm
  map_comp c c' c'' := by
    apply moduleHom_ext
    intro b
    rw [Category.assoc, moduleHomEquiv_symm_π]
    change eComp (Complex A) c c' c'' ≫ (a c c'').app (op b) =
      (_ ⊗ₘ _) ≫ moduleComposition A B (P c) (P c') (P c'') ≫
        moduleHomπ A B (P c) (P c'') b
    rw [moduleComposition_π, tensorHom_comp_tensorHom_assoc,
      moduleHomEquiv_symm_π, moduleHomEquiv_symm_π]
    exact hc c c' c'' (op b)

/-- 構成子の左作用を取り出すと元の作用族になる。 -/
lemma ofParamTrans_map_π (P : C → RightModule A B) (a hi hc) (c c' : C) (b : B) :
    (ofParamTrans A B C P a hi hc).toFunctor.map c c' ≫
      moduleHomπ A B (P c) (P c') b = (a c c').app (op b) :=
  moduleHomEquiv_symm_π A B _ _ _ _ b

variable {A B C}

/-- bimoduleから全次数自然な左作用族を取り出す。 -/
def paramTrans (M : Bimodule A B C) (c c' : C) :
    ModuleParamTrans A B (c ⟶[Complex A] c') (M.rightAt c) (M.rightAt c') :=
  moduleHomEquiv A B _ _ _ (M.toFunctor.map c c')

lemma paramTrans_unit (M : Bimodule A B C) (c : C) (b : Bᵒᵖ) :
    eId (Complex A) c ≫ (M.paramTrans c c).app b = identity ((M.rightAt c).obj b) := by
  change eId (Complex A) c ≫ M.toFunctor.map c c ≫
    moduleHomπ A B (M.rightAt c) (M.rightAt c) b.unop = _
  rw [← Category.assoc, M.toFunctor.map_id]
  exact moduleIdentity_π A B (M.rightAt c) b.unop

lemma paramTrans_comp (M : Bimodule A B C) (c c' c'' : C) (b : Bᵒᵖ) :
    eComp (Complex A) c c' c'' ≫ (M.paramTrans c c'').app b =
      ((M.paramTrans c c').app b ⊗ₘ (M.paramTrans c' c'').app b) ≫
        enrichedComposition _ _ _ := by
  change eComp (Complex A) c c' c'' ≫ M.toFunctor.map c c'' ≫
    moduleHomπ A B (M.rightAt c) (M.rightAt c'') b.unop = _
  rw [← Category.assoc, M.toFunctor.map_comp]
  change (M.toFunctor.map c c' ⊗ₘ M.toFunctor.map c' c'') ≫
    moduleComposition A B (M.rightAt c) (M.rightAt c') (M.rightAt c'') ≫
      moduleHomπ A B (M.rightAt c) (M.rightAt c'') b.unop = _
  rw [moduleComposition_π, tensorHom_comp_tensorHom_assoc]
  rfl

/-- 抽出した作用族からbimoduleを再構成すると元に戻る。 -/
lemma ofParamTrans_recover (M : Bimodule A B C) :
    ofParamTrans A B C M.rightAt M.paramTrans M.paramTrans_unit M.paramTrans_comp = M := by
  change (ofParamTrans A B C M.rightAt M.paramTrans
    M.paramTrans_unit M.paramTrans_comp).toFunctor = M.toFunctor
  apply EnrichedFunctor.ext (Complex A)
    (F := (ofParamTrans A B C M.rightAt M.paramTrans
      M.paramTrans_unit M.paramTrans_comp).toFunctor) (G := M.toFunctor) (fun _ => rfl)
  intro c c'
  change (moduleHomEquiv A B _ _ _).symm
    ((moduleHomEquiv A B _ _ _) (M.toFunctor.map c c')) ≫ 𝟙 _ = M.toFunctor.map c c'
  simp

end SerrePositivity.DifferentialGraded.Bimodule
end

end OfActions

/-! ## ClosedTransforms（旧 SerrePositivity/DifferentialGraded/Bimodule/ClosedTransforms.lean） -/

/-! # 全Hom自然なbimoduleの閉零豊穣自然変換 -/

@[expose] public section ClosedTransforms
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory BraidedCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 左C作用も全Homに関して自然な、パラメータ付きbimodule変換。 -/
abbrev BimoduleParamTrans (K : Complex A) (M N : Bimodule A B C) :=
  GradedNatTrans ((Center.ofBraided (Complex A)).obj K) M.toFunctor N.toFunctor

namespace Bimodule

/-- 右B加群射族の全Hom可換式から、左C作用に関する豊穣自然性を得る。 -/
lemma closedFamily_naturality {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ⟶
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c') =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c)) (c c' : C) :
    (β_ (𝟙_ (Complex A)) (c ⟶[Complex A] c')).hom ≫
      (M.toFunctor.map c c' ⊗ₘ ForgetEnrichment.homTo (Complex A) (a c')) ≫
        eComp (Complex A) (M.rightAt c) (M.rightAt c') (N.rightAt c') =
    (ForgetEnrichment.homTo (Complex A) (a c) ⊗ₘ N.toFunctor.map c c') ≫
      eComp (Complex A) (M.rightAt c) (N.rightAt c) (N.rightAt c') := by
  apply (cancel_epi (λ_ (c ⟶[Complex A] c')).inv).1
  rw [braiding_tensorUnit_left]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [rightUnitor_inv_comp_tensorHom_assoc, leftUnitor_inv_comp_tensorHom_assoc]
  exact h c c'

/-- 全次数自然な右加群射族を、単位パラメータのbimodule豊穣自然変換に束ねる。 -/
def closedFamilyTrans {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ⟶
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c') =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c)) :
    BimoduleParamTrans A B C (𝟙_ (Complex A)) M N where
  app c := ForgetEnrichment.homTo (Complex A) (a c)
  naturality := closedFamily_naturality A B C a h

@[simp]
lemma closedFamilyTrans_app {M N : Bimodule A B C} (a) (h) (c : C) :
    (closedFamilyTrans A B C (M := M) (N := N) a h).app c =
      ForgetEnrichment.homTo (Complex A) (a c) := rfl

end Bimodule
end SerrePositivity.DifferentialGraded
end

end ClosedTransforms

/-! ## ClosedIso（旧 SerrePositivity/DifferentialGraded/Bimodule/ClosedIso.lean） -/

/-! # 全Hom自然なbimodule同型族の順逆の閉零変換 -/

@[expose] public section ClosedIso
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma isoFamily_inv_naturality {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ≅
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c').hom =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c).hom)
    (c c' : C) :
    N.toFunctor.map c c' ≫
      moduleHomPostcompose A B (N.rightAt c) (N.rightAt c') (M.rightAt c') (a c').inv =
    M.toFunctor.map c c' ≫
      moduleHomPrecompose A B (N.rightAt c) (M.rightAt c) (M.rightAt c') (a c).inv := by
  exact moduleHom_iso_square_inv A B (M.toFunctor.map c c') (N.toFunctor.map c c')
    (a c) (a c') (h c c')

/-- 全Hom自然な右加群同型族の順方向の単位パラメータ変換。 -/
def isoFamilyHom {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ≅
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c').hom =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c).hom)
    : BimoduleParamTrans A B C (𝟙_ (Complex A)) M N :=
  closedFamilyTrans A B C (fun c => (a c).hom) h

/-- 同じ同型族の逆方向も全Homに関して豊穣自然。 -/
def isoFamilyInv {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ≅
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c').hom =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c).hom)
    : BimoduleParamTrans A B C (𝟙_ (Complex A)) N M :=
  closedFamilyTrans A B C (fun c => (a c).inv) (isoFamily_inv_naturality A B C a h)

@[simp]
lemma isoFamilyHom_app {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ≅
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c').hom =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c).hom)
    (c : C) :
    (isoFamilyHom A B C a h).app c =
      ForgetEnrichment.homTo (Complex A) (a c).hom := rfl

@[simp]
lemma isoFamilyInv_app {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ≅
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c').hom =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c).hom)
    (c : C) :
    (isoFamilyInv A B C a h).app c =
      ForgetEnrichment.homTo (Complex A) (a c).inv := rfl

/-- 順逆の成分合成は主Homの閉単位元に一致する。 -/
lemma isoFamily_hom_inv_app {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ≅
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c').hom =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c).hom)
    (c : C) :
    (λ_ (𝟙_ (Complex A))).inv ≫
      ((isoFamilyHom A B C a h).app c ⊗ₘ (isoFamilyInv A B C a h).app c) ≫
      eComp (Complex A) (M.rightAt c) (N.rightAt c) (M.rightAt c) =
      eId (Complex A) (M.rightAt c) :=
  moduleIso_closed_hom_inv A B (a c)

/-- 順逆の成分合成は主Homの閉単位元に一致する。 -/
lemma isoFamily_inv_hom_app {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ≅
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c').hom =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c).hom)
    (c : C) :
    (λ_ (𝟙_ (Complex A))).inv ≫
      ((isoFamilyInv A B C a h).app c ⊗ₘ (isoFamilyHom A B C a h).app c) ≫
      eComp (Complex A) (N.rightAt c) (M.rightAt c) (N.rightAt c) =
      eId (Complex A) (N.rightAt c) :=
  moduleIso_closed_hom_inv A B (a c).symm

end SerrePositivity.DifferentialGraded.Bimodule
end

end ClosedIso

/-! ## ClosedComponents（旧 SerrePositivity/DifferentialGraded/Bimodule/ClosedComponents.lean） -/

/-! # 閉零bimodule変換の右加群射成分と全Hom自然性 -/

@[expose] public section ClosedComponents
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory BraidedCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma closedFamily_naturality_converse {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ⟶
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ (c c' : C), (β_ (𝟙_ (Complex A)) (c ⟶[Complex A] c')).hom ≫
      (M.toFunctor.map c c' ⊗ₘ ForgetEnrichment.homTo (Complex A) (a c')) ≫
        eComp (Complex A) (M.rightAt c) (M.rightAt c') (N.rightAt c') =
      (ForgetEnrichment.homTo (Complex A) (a c) ⊗ₘ N.toFunctor.map c c') ≫
        eComp (Complex A) (M.rightAt c) (N.rightAt c) (N.rightAt c')) (c c' : C) :
    M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c') =
    N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c) := by
  have hh := congrArg (fun k => (λ_ (c ⟶[Complex A] c')).inv ≫ k) (h c c')
  rw [braiding_tensorUnit_left] at hh
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at hh
  rw [rightUnitor_inv_comp_tensorHom_assoc, leftUnitor_inv_comp_tensorHom_assoc] at hh
  exact hh

/-- 単位パラメータの全豊穣変換を右B加群射として評価する。 -/
def closedTransApp {M N : Bimodule A B C}
    (τ : BimoduleParamTrans A B C (𝟙_ (Complex A)) M N) (c : C) :
    ForgetEnrichment.of (Complex A) (M.rightAt c) ⟶
      ForgetEnrichment.of (Complex A) (N.rightAt c) :=
  ForgetEnrichment.homOf (Complex A) (τ.app c)

lemma closedTransApp_naturality {M N : Bimodule A B C}
    (τ : BimoduleParamTrans A B C (𝟙_ (Complex A)) M N) (c c' : C) :
    M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c')
        (closedTransApp A B C τ c') =
    N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c')
        (closedTransApp A B C τ c) := by
  apply closedFamily_naturality_converse A B C (closedTransApp A B C τ)
  intro x y
  have ht := τ.naturality x y
  change (β_ (𝟙_ (Complex A)) (x ⟶[Complex A] y)).hom ≫
    (M.toFunctor.map x y ⊗ₘ τ.app y) ≫
      eComp (Complex A) (M.rightAt x) (M.rightAt y) (N.rightAt y) =
    (τ.app x ⊗ₘ N.toFunctor.map x y) ≫
      eComp (Complex A) (M.rightAt x) (N.rightAt x) (N.rightAt y) at ht
  simpa only [closedTransApp, ForgetEnrichment.homTo_homOf] using ht

@[simp]
lemma closedTransApp_closedFamilyTrans {M N : Bimodule A B C} (a) (h) (c : C) :
    closedTransApp A B C (closedFamilyTrans A B C (M := M) (N := N) a h) c = a c := rfl

lemma closedFamilyTrans_closedTransApp {M N : Bimodule A B C}
    (τ : BimoduleParamTrans A B C (𝟙_ (Complex A)) M N) :
    closedFamilyTrans A B C (closedTransApp A B C τ)
      (closedTransApp_naturality A B C τ) = τ := by
  apply GradedNatTrans.ext
  funext c
  exact ForgetEnrichment.homTo_homOf (Complex A) (τ.app c)

end SerrePositivity.DifferentialGraded.Bimodule
end

end ClosedComponents

/-! ## ClosedMapFamily（旧 SerrePositivity/DifferentialGraded/Bimodule/ClosedMapFamily.lean） -/

/-! # 全Hom自然な右加群射族による閉零bimodule射の表示 -/

@[expose] public section ClosedMapFamily
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 右B加群射を成分とし、左C作用の全Hom自然性を持つ射族。 -/
abbrev ClosedMapFamily (M N : Bimodule A B C) :=
  {a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ⟶
      ForgetEnrichment.of (Complex A) (N.rightAt c) //
    ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c') =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c)}

/-- 単位パラメータの全次数変換と全Hom自然な加群射族の同値。 -/
def closedMapFamilyEquiv (M N : Bimodule A B C) :
    BimoduleParamTrans A B C (𝟙_ (Complex A)) M N ≃ ClosedMapFamily A B C M N where
  toFun τ := ⟨closedTransApp A B C τ, closedTransApp_naturality A B C τ⟩
  invFun a := closedFamilyTrans A B C a.val a.property
  left_inv := closedFamilyTrans_closedTransApp A B C
  right_inv a := by apply Subtype.ext; rfl

/-- 閉零bimodule射族の恒等射。 -/
def closedMapFamilyId (M : Bimodule A B C) : ClosedMapFamily A B C M M :=
  ⟨fun _ => 𝟙 _, fun c c' => moduleHom_square_id A B (M.toFunctor.map c c')⟩

/-- 全次数自然性を保つbimodule射族の合成。 -/
def closedMapFamilyComp {M N P : Bimodule A B C}
    (a : ClosedMapFamily A B C M N) (b : ClosedMapFamily A B C N P) :
    ClosedMapFamily A B C M P :=
  ⟨fun c => a.val c ≫ b.val c, fun c c' =>
    moduleHom_square_comp A B (M.toFunctor.map c c') (N.toFunctor.map c c')
      (P.toFunctor.map c c') (a.val c) (a.val c') (b.val c) (b.val c')
      (a.property c c') (b.property c c')⟩

end SerrePositivity.DifferentialGraded.Bimodule
end

end ClosedMapFamily

/-! ## Category（旧 SerrePositivity/DifferentialGraded/Bimodule/Category.lean） -/

/-! # 全Hom自然な閉零射を持つbimoduleの圏 -/

@[expose] public section Category
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 対象は既存のbimodule、射は全Hom自然な閉零射。 -/
def BimoduleCategory := Bimodule A B C

namespace BimoduleCategory

/-- 既存のbimoduleを閉零射の圏の対象として読む。 -/
def of (M : Bimodule A B C) : BimoduleCategory A B C := M

/-- 閉零射の圏の対象から元のbimoduleを取り出す。 -/
def underlying (M : BimoduleCategory A B C) : Bimodule A B C := M

instance category : Category (BimoduleCategory A B C) where
  Hom M N := Bimodule.ClosedMapFamily A B C (underlying A B C M) (underlying A B C N)
  id M := Bimodule.closedMapFamilyId A B C (underlying A B C M)
  comp a b := Bimodule.closedMapFamilyComp A B C a b
  id_comp := by
    intro M N a
    apply Subtype.ext
    funext c
    exact Category.id_comp (a.val c)
  comp_id := by
    intro M N a
    apply Subtype.ext
    funext c
    exact Category.comp_id (a.val c)
  assoc := by
    intro M N P Q a b d
    apply Subtype.ext
    funext c
    exact Category.assoc (a.val c) (b.val c) (d.val c)

/-- 閉零射を元のMathlib GradedNatTransへ戻す。 -/
def homEquiv (M N : BimoduleCategory A B C) :
    (M ⟶ N) ≃ BimoduleParamTrans A B C (𝟙_ (Complex A)) (underlying A B C M) (underlying A B C N) :=
  (Bimodule.closedMapFamilyEquiv A B C (underlying A B C M) (underlying A B C N)).symm

end BimoduleCategory
end SerrePositivity.DifferentialGraded
end

end Category

/-! ## Evaluation（旧 SerrePositivity/DifferentialGraded/Bimodule/Evaluation.lean） -/

/-! # 閉零bimodule圏の評価と全次数変換への復元 -/

@[expose] public section Evaluation
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 左対象を固定した、全次数自然な右加群への評価。 -/
def evaluation (c : C) : BimoduleCategory A B C ⥤ ModuleCategory A B where
  obj M := ForgetEnrichment.of (Complex A) ((underlying A B C M).rightAt c)
  map a := a.val c

@[ext]
lemma hom_ext {M N : BimoduleCategory A B C} {a b : M ⟶ N}
    (h : ∀ c, (evaluation A B C c).map a = (evaluation A B C c).map b) : a = b := by
  apply Subtype.ext
  funext c
  exact h c

@[simp]
lemma homEquiv_app {M N : BimoduleCategory A B C} (a : M ⟶ N) (c : C) :
    (homEquiv A B C M N a).app c =
      ForgetEnrichment.homTo (Complex A) ((evaluation A B C c).map a) := rfl

lemma homEquiv_comp_app {M N P : BimoduleCategory A B C} (a : M ⟶ N) (b : N ⟶ P)
    (c : C) :
    (homEquiv A B C M P (a ≫ b)).app c =
    (λ_ (𝟙_ (Complex A))).inv ≫
      ((homEquiv A B C M N a).app c ⊗ₘ (homEquiv A B C N P b).app c) ≫
      eComp (Complex A) ((underlying A B C M).rightAt c)
        ((underlying A B C N).rightAt c) ((underlying A B C P).rightAt c) := by
  change ForgetEnrichment.homTo (Complex A) (a.val c ≫ b.val c) =
    (λ_ (𝟙_ (Complex A))).inv ≫
      (ForgetEnrichment.homTo (Complex A) (a.val c) ⊗ₘ
        ForgetEnrichment.homTo (Complex A) (b.val c)) ≫ _
  exact (ForgetEnrichment.homTo_comp (Complex A) (a.val c) (b.val c)).trans
    (Category.assoc _ _ _)

end SerrePositivity.DifferentialGraded.BimoduleCategory
end

end Evaluation

/-! ## Isomorphism（旧 SerrePositivity/DifferentialGraded/Bimodule/Isomorphism.lean） -/

/-! # 全Hom自然な同型族からの閉零bimodule同型 -/

@[expose] public section Isomorphism
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 全Hom自然な右加群同型族から、閉零bimodule圏の同型を構成する。 -/
def isoOfFamily {M N : BimoduleCategory A B C}
    (a : ∀ c, (evaluation A B C c).obj M ≅ (evaluation A B C c).obj N)
    (h : ∀ c c', (underlying A B C M).toFunctor.map c c' ≫
      moduleHomPostcompose A B ((underlying A B C M).rightAt c)
        ((underlying A B C M).rightAt c') ((underlying A B C N).rightAt c') (a c').hom =
      (underlying A B C N).toFunctor.map c c' ≫
      moduleHomPrecompose A B ((underlying A B C M).rightAt c)
        ((underlying A B C N).rightAt c) ((underlying A B C N).rightAt c') (a c).hom) :
    M ≅ N where
  hom := ⟨fun c => (a c).hom, h⟩
  inv := ⟨fun c => (a c).inv, Bimodule.isoFamily_inv_naturality A B C a h⟩
  hom_inv_id := by
    apply Subtype.ext
    funext c
    exact (a c).hom_inv_id
  inv_hom_id := by
    apply Subtype.ext
    funext c
    exact (a c).inv_hom_id

@[simp]
lemma isoOfFamily_hom_eval {M N : BimoduleCategory A B C} (a) (h) (c : C) :
    (evaluation A B C c).map (isoOfFamily A B C (M := M) (N := N) a h).hom =
      (a c).hom := rfl

@[simp]
lemma isoOfFamily_inv_eval {M N : BimoduleCategory A B C} (a) (h) (c : C) :
    (evaluation A B C c).map (isoOfFamily A B C (M := M) (N := N) a h).inv =
      (a c).inv := rfl

end SerrePositivity.DifferentialGraded.BimoduleCategory
end

end Isomorphism
