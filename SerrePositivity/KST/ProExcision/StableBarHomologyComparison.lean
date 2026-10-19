module
public import SerrePositivity.KST.ProExcision.BarSequentialColimits
public import SerrePositivity.KST.ProExcision.HomologyModelSequentialColimits
public import SerrePositivity.KST.ProExcision.RelativeModuleSequentialColimit

/-!
# 実安定 bar ホモロジーと有限 rank の実余極限

概要：実安定モノイドの bar の H_* と有限 rank の実 H_* の余極限を比較する。
方針：実 bar と既存の自然な実ホモロジー模型の保存性を合成し、相対商へ降ろす。
規約：KST Proposition 4.14、SW92 Lemma 1.4。比較同型を新しい入力にしない。
使われ方：有限 rank の実相対零化を安定相対ホモロジーへ移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits Comparison

/-- 概要：実安定モノイドの bar の H_* と有限段階の H_* の余極限の実同型。
方針：実 bar と借用する自然な複体模型から証明した順序余極限保存を合成する。
規約：SW92 Lemma 1.4。使われ方：安定相対項の実模型比較。 -/
def SimplicialHomologyModel.barSequentialColimitIso
    {F : SSet.{u} ⥤ ModuleCat.{u} ℤ} {i : ℕ} (M : SimplicialHomologyModel F i)
    (D : ℕ ⥤ SimplicialObject MonCat.{u}) :
    F.obj (monoidBar (colimit D)) ≅ colimit (D ⋙ monoidBarFunctor ⋙ F) := by
  letI := M.preservesSequentialColimits
  exact preservesColimitIso (monoidBarFunctor ⋙ F) D

/-- 概要：実安定 bar ホモロジーの比較は実 rank 図式の射に自然。
方針：実順序余極限保存の標準自然同型の自然性を使う。
規約：KST Proposition 4.14、SW92 Lemma 1.4。
使われ方：標準包含と指定元の乗法の実正方形。 -/
lemma SimplicialHomologyModel.barSequentialColimitIso_natural
    {F : SSet.{u} ⥤ ModuleCat.{u} ℤ} {i : ℕ} (M : SimplicialHomologyModel F i)
    {A B : ℕ ⥤ SimplicialObject MonCat.{u}} (f : A ⟶ B) :
    F.map (monoidBarMap (colimMap f)) ≫ (M.barSequentialColimitIso B).hom =
      (M.barSequentialColimitIso A).hom ≫
        colimMap (Functor.whiskerRight f (monoidBarFunctor ⋙ F)) := by
  letI := M.preservesSequentialColimits
  exact (preservesColimitNatIso (monoidBarFunctor ⋙ F)).hom.naturality f

/-- 概要：実安定 bar の相対 H_* と有限 rank の実相対 H_* の余極限の実同型。
方針：実標準包含の H_* 正方形を実通常商へ降ろし、その実商と余極限を交換する。
規約：KST Proposition 4.14、SW92 Lemma 1.4。filtered 保存や相対比較を入力に隠さない。
使われ方：有限 rank の実零化を安定相対ホモロジーへ移す。 -/
def SimplicialHomologyModel.relativeBarSequentialColimitIso
    {F : SSet.{u} ⥤ ModuleCat.{u} ℤ} {i : ℕ} (M : SimplicialHomologyModel F i)
    {A B : ℕ ⥤ SimplicialObject MonCat.{u}} (s : A ⟶ B) :
    relativeModule (F.map (monoidBarMap (colimMap s))) ≅
      colimit (relativeModuleDiagram (Functor.whiskerRight s (monoidBarFunctor ⋙ F))) :=
  relativeModuleIso _ _ (M.barSequentialColimitIso A) (M.barSequentialColimitIso B)
      (M.barSequentialColimitIso_natural s) ≪≫
    relativeModuleSequentialColimitIso (Functor.whiskerRight s (monoidBarFunctor ⋙ F))

end SerrePositivity.KST.ProExcision
