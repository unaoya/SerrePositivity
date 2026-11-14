module

public import SerrePositivity.Archive.KST.DescentConditional.FamilyCechFunctorComparison
public import SerrePositivity.Archive.KST.DescentConditional.FiniteFamilyCechFunctor

/-!
# 関手で幾何を移した被覆族の前層の指定比較

## 概要
有限 wide pullback を保つ関手に沿う前層の制限は、元の被覆族の指定空間図式を保つ。

## 方針
構成済みの幾何の指定同型を反変前層で写し、有限積で束ねる。

## 規約
単体射と元の指定増強を同時に保つ実際の同型とする。

## 使われ方
論文 公理 (1)、補題 3.2 の Over 上の transfer の局所検査。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w t z r s

open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {D : Type w} [Category.{t} D] [HasFiniteLimits D] (G : C ⥤ D)
  [∀ n : ℕ, PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1))) G]
  {ι : Type z} [Finite ι] {Y : C} (X : ι → C) (cover : ∀ i, X i ⟶ Y)
  {V : Type r} [Category.{s} V] [HasFiniteProducts V] (F : Dᵒᵖ ⥤ V)

/-- 概要：幾何を関手で移す前後の被覆族の余単体図式の指定同型（公理 (1)）。
方針：指定幾何同型の逆を前層で写し、各次数で有限積にする。
規約：全単体射への自然性を保つ。使われ方：Over の忘却に沿う実降下の移送。 -/
def familyCechFunctorDiagramIso :
    familyCechDiagram X cover (G.op ⋙ F) ≅
      familyCechDiagram (fun i ↦ G.obj (X i)) (fun i ↦ G.map (cover i)) F :=
  NatIso.ofComponents
    (fun n ↦ Pi.mapIso (fun a : Fin (n.len + 1) → ι ↦
      F.mapIso (familyCechTermFunctorIso G X cover n a).symm.op))
    (by
      intro n m f
      apply Pi.hom_ext
      intro a
      have h := congrArg (fun q ↦ F.map q.op)
        (familyCechTermFunctorIso_inv_naturality G X cover f a)
      simp only [op_comp, F.map_comp] at h
      simpa [familyCechDiagram, familyCechValueMap, Category.assoc] using
        congrArg (Pi.π
          (fun b : Fin (n.len + 1) → ι ↦ F.obj (op (G.obj (familyCechTerm X cover n b))))
          (fun j ↦ a (f.toOrderHom j)) ≫ ·) h)

/-- 概要：幾何を写す指定図式同型は元の指定増強を保つ（公理 (1)）。
方針：積射影で元の基底射と指定同型の基底射影の式を比較する。
規約：増強元は同じ値であり恒等比較。使われ方：増強つき図式の同型。 -/
theorem familyCechFunctorDiagramIso_augmentation (n : SimplexCategory) :
    (familyCechAugmentation X cover (G.op ⋙ F)).app n ≫
        (familyCechFunctorDiagramIso G X cover F).hom.app n =
      (familyCechAugmentation (fun i ↦ G.obj (X i)) (fun i ↦ G.map (cover i)) F).app n := by
  apply Pi.hom_ext
  intro a
  have h := familyCechTermFunctorIso_hom_base G X cover n a
  have hi : (familyCechTermFunctorIso G X cover n a).inv ≫
      G.map (WidePullback.base (fun j ↦ cover (a j))) =
        WidePullback.base (fun j ↦ G.map (cover (a j))) := by
    rw [← h]
    simp
  have he := congrArg (fun q ↦ F.map q.op) hi
  simp only [op_comp, F.map_comp] at he
  simpa [familyCechAugmentation, familyCechFunctorDiagramIso,
    Category.assoc] using he

/-- 概要：幾何を写す前後の被覆族の指定増強つき空間図式は同型（公理 (1)）。
方針：増強元の恒等と指定図式同型を、証明済みの増強の可換式で束ねる。
規約：有限 wide pullback の保存だけを使う。使われ方：Over 上の元の前層の実降下。 -/
def familyCechFunctorSpaceIso (F : Dᵒᵖ ⥤ SSet.{0}) :
    familyCechSpace X cover (G.op ⋙ F) ≅
      familyCechSpace (fun i ↦ G.obj (X i)) (fun i ↦ G.map (cover i)) F :=
  Comma.isoMk (Iso.refl _) (familyCechFunctorDiagramIso G X cover F) (by
    apply NatTrans.ext
    funext n
    exact (Category.id_comp _).trans
      (familyCechFunctorDiagramIso_augmentation G X cover F n).symm)

end SerrePositivity.KST.Descent
