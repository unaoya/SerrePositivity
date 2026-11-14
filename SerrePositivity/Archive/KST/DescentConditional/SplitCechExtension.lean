module

public import SerrePositivity.Archive.KST.DescentConditional.BottomSimplex
public import SerrePositivity.KST.Descent.SplitCech

/-!
# 切断を持つ Čech nerve の最小元つき添字への拡張

## 概要
切断を持つ射の実際の Čech nerve を、最小元を保つ添字圏の反対圏全体へ拡張する。

## 方針
最小元以外の座標の wide pullback を取り、最小元の座標は切断と基底射の合成で与える。

## 規約
空の座標の段も保持する。有限極限と実際の切断以外の降下仮定は使わない。

## 使われ方
論文 補題 3.2 の分裂余単体対象の実降下。τ 位相の層論を Čech 計算で置換する幾何入力。
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {X Y : C} (f : X ⟶ Y) (s : SplitEpi f)

/-- 概要：最小元以外の座標での実際の Čech 段（補題 3.2）。
方針：同じ基底への指定 wide pullback を取る。
規約：座標が空の段も含む。使われ方：分裂 Čech の拡張の対象。 -/
abbrev splitCechTerm (n : BottomSimplex) : C :=
  widePullback Y (fun _ : Fin n.obj.len ↦ X) (fun _ ↦ f)

/-- 概要：最小元も許す実際の Čech 座標の評価（補題 3.2）。
方針：最小元は基底射と切断、後続元は指定射影。
規約：切断は固定する。使われ方：最小元を保つ射による座標の引き戻し。 -/
def splitCechPoint (n : BottomSimplex) (j : Fin (n.obj.len + 1)) : splitCechTerm f n ⟶ X :=
  Fin.cases (WidePullback.base (fun _ : Fin n.obj.len ↦ f) ≫ s.section_)
    (fun i ↦ WidePullback.π (fun _ : Fin n.obj.len ↦ f) i) j

/-- 概要：最小元を含む各座標は同じ基底上にある（補題 3.2）。
方針：零では切断恒等式、後続元では wide pullback の可換式。
規約：射の等式で検査する。使われ方：拡張図式の射の構成。 -/
theorem splitCechPoint_over (n : BottomSimplex) (j : Fin (n.obj.len + 1)) :
    splitCechPoint f s n j ≫ f = WidePullback.base (fun _ : Fin n.obj.len ↦ f) := by
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · change (_ ≫ s.section_) ≫ f = _
    rw [Category.assoc, s.id, Category.comp_id]
  · exact WidePullback.π_arrow _ _

/-- 概要：最小元を保つ添字射に沿う実際の Čech 射（補題 3.2）。
方針：各非最小座標の像を指定して wide pullback へ持ち上げる。
規約：最小元へ潰れる座標には固定した切断を使う。使われ方：拡張図式の関手性。 -/
def splitCechMap {n m : BottomSimplex} (a : n ⟶ m) : splitCechTerm f m ⟶ splitCechTerm f n :=
  WidePullback.lift (WidePullback.base (fun _ : Fin m.obj.len ↦ f))
    (fun i ↦ splitCechPoint f s m (a.hom.toOrderHom i.succ))
    (fun i ↦ splitCechPoint_over f s m (a.hom.toOrderHom i.succ))

/-- 概要：指定 Čech 射は最小元を含む全座標と可換（補題 3.2）。
方針：零では最小元の保存、後続元では指定 lift の射影公式。
規約：全座標の式を保持。使われ方：拡張図式の合成則。 -/
theorem splitCechMap_point {n m : BottomSimplex} (a : n ⟶ m)
    (j : Fin (n.obj.len + 1)) :
    splitCechMap f s a ≫ splitCechPoint f s n j =
      splitCechPoint f s m (a.hom.toOrderHom j) := by
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · change splitCechMap f s a ≫
      (WidePullback.base (fun _ : Fin n.obj.len ↦ f) ≫ s.section_) = _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ s.section_)
        (show splitCechMap f s a ≫ WidePullback.base (fun _ : Fin n.obj.len ↦ f) =
            WidePullback.base (fun _ : Fin m.obj.len ↦ f) from
          WidePullback.lift_base _ _ _ _)).trans
        (congrArg (splitCechPoint f s m) a.property.symm))
  · exact WidePullback.lift_π _ _ _ _ i

/-- 概要：切断を持つ射の実際の拡張 Čech 図式（補題 3.2）。
方針：最小元を含む座標の可換式と wide pullback の一意性で関手性を示す。
規約：空の座標の段を含む実際の幾何図式。使われ方：任意の前層で写す分裂余単体対象。 -/
def splitCechExtension : BottomSimplexᵒᵖ ⥤ C where
  obj n := splitCechTerm f n.unop
  map a := splitCechMap f s a.unop
  map_id n := by
    apply WidePullback.hom_ext
    · intro i
      simp only [splitCechMap, WidePullback.lift_π, Category.id_comp]
      rfl
    · simp only [splitCechMap, WidePullback.lift_base, Category.id_comp]
  map_comp {n m l} a b := by
    apply WidePullback.hom_ext
    · intro i
      simp only [splitCechMap, WidePullback.lift_π, Category.assoc]
      exact (splitCechMap_point f s a.unop _).symm
    · simp only [splitCechMap, WidePullback.lift_base, Category.assoc]

/-- 概要：最小元の付加への制限は元の実際の Čech nerve と同型（補題 3.2）。
方針：非最小座標と元の Čech 座標が一致することを定義で検査する。
規約：対象だけでなく全射が同じ。使われ方：元の幾何的 Čech の指定増強への接続。 -/
def splitCechExtensionRestrictionIso :
    BottomSimplex.adjoin.op ⋙ splitCechExtension f s ≅ (Arrow.mk f).cechNerve :=
  Iso.refl _

/-- 概要：拡張 Čech の全段から元の基底への指定増強（補題 3.2）。
方針：各 wide pullback の基底射と指定 lift の可換式を使う。
規約：空の座標の段でも同じ基底射。使われ方：元の前層による指定増強。 -/
def splitCechExtensionAugmentation :
    splitCechExtension f s ⟶ (Functor.const BottomSimplexᵒᵖ).obj Y where
  app n := WidePullback.base (fun _ : Fin n.unop.obj.len ↦ f)
  naturality {_ _} _ :=
    (WidePullback.lift_base _ _ _ _).trans (Category.comp_id _).symm

/-- 概要：座標が空の段は指定基底射で元の基底と同型（補題 3.2）。
方針：空族からの lift と wide pullback の一意性を使う。
規約：基底射そのものを同型の hom にする。使われ方：始対象での増強値の同定。 -/
def splitCechEmptyIso : splitCechTerm f ⟨⦋0⦌⟩ ≅ Y where
  hom := WidePullback.base (fun _ : Fin 0 ↦ f)
  inv := WidePullback.lift (𝟙 Y) (fun i : Fin 0 ↦ i.elim0) (fun i ↦ i.elim0)
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro i; exact i.elim0
    · simp only [Category.assoc, WidePullback.lift_base, Category.comp_id, Category.id_comp]
  inv_hom_id := WidePullback.lift_base _ _ _ _

/-- 概要：元の Čech への制限は指定増強も保持（補題 3.2）。
方針：最小元以外の座標の基底射の定義を検査する。
規約：単なる図式同型だけでなく実際の指定増強の等式。
使われ方：元の前層の指定比較との接続。 -/
theorem splitCechExtensionAugmentation_restriction :
    Functor.whiskerLeft BottomSimplex.adjoin.op (splitCechExtensionAugmentation f s) =
      (Arrow.mk f).augmentedCechNerve.hom := rfl

variable {V : Type*} [Category* V]

/-- 概要：元の前層による拡張 Čech の実際の余単体図式（補題 3.2）。
方針：幾何図式を反対圏へ移し、元の前層を前合成する。
規約：元の前層を任意の別データへ交換しない。使われ方：分裂側の実際の空間図式。 -/
def splitCechPresheafExtension (F : Cᵒᵖ ⥤ V) : BottomSimplex ⥤ V :=
  (splitCechExtension f s).rightOp ⋙ F

/-- 概要：元の前層の値から拡張 Čech への実際の指定増強（補題 3.2）。
方針：幾何の指定増強を反変に写す。
規約：空の座標の段の値も保持する。使われ方：始対象での計算との接続。 -/
def splitCechPresheafExtensionAugmentation (F : Cᵒᵖ ⥤ V) :
    (Functor.const BottomSimplex).obj (F.obj (op Y)) ⟶ splitCechPresheafExtension f s F :=
  (Functor.constComp BottomSimplex (op Y) F).inv ≫
    Functor.whiskerRight (splitCechExtensionAugmentation f s).rightOp F

/-- 概要：前層の拡張 Čech の制限は元の実際の Čech の像（補題 3.2）。
方針：指定幾何図式の制限の一致を元の前層で写す。
規約：全射についての自然同型。使われ方：分裂降下を元の Čech 比較へ移す。 -/
def splitCechPresheafExtensionRestrictionIso (F : Cᵒᵖ ⥤ V) :
    BottomSimplex.adjoin ⋙ splitCechPresheafExtension f s F ≅
      (Arrow.mk f).cechNerve.rightOp ⋙ F := Iso.refl _

/-- 概要：始対象での前層の指定増強は基底射の指定同型の像（補題 3.2）。
方針：空座標の同型の hom が基底射そのものであることを使う。
規約：指定増強そのものの等式。使われ方：分裂側の増強値の同定。 -/
theorem splitCechPresheafExtensionAugmentation_empty (F : Cᵒᵖ ⥤ V) :
    (splitCechPresheafExtensionAugmentation f s F).app ⟨⦋0⦌⟩ =
      (F.mapIso (splitCechEmptyIso f).op).hom := Category.id_comp _

/-- 概要：始対象での前層の指定増強は実際に同型（補題 3.2）。
方針：指定増強を元の基底射の同型の像に同定する。
規約：分裂 Čech の全体の降下はまだ結論しない。使われ方：始対象での実際の比較の計算。 -/
instance splitCechPresheafExtensionAugmentation_empty_isIso (F : Cᵒᵖ ⥤ V) :
    IsIso ((splitCechPresheafExtensionAugmentation f s F).app ⟨⦋0⦌⟩) := by
  rw [splitCechPresheafExtensionAugmentation_empty]
  exact (F.mapIso (splitCechEmptyIso f).op).isIso_hom

end SerrePositivity.KST.Descent
