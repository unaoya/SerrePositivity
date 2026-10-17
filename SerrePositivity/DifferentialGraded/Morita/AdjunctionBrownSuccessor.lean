module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionBrownRelations
public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # 生成元の関係を消す表現対象近似の後続段階

## 概要
射L(X)→Yを、全ての生成元の関係を殺すX→X'に沿って延長する。

## 方針
全関係の余積からの射をdistinguished三角形に補完し、L像のHom完全性で延長射を得る。

## 規約と注意
Lの三角性と指定余積の保存を明示する。随伴の存在や表現可能性は仮定しない。

## 使われ方
U16aの一般右随伴を、初期被覆から可算telescopeへ構成するための後続操作。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (L : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  {X : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E} (r : L.obj X ⟶ Y)

/-- 同じ標的射を延長し、生成元から来る全関係を消す一つの後続段階。 -/
structure BrownSuccessor where
  obj : DerivedModuleCategory A D
  map : X ⟶ obj
  target : L.obj obj ⟶ Y
  fac : L.map map ≫ target = r
  kills : ∀ (p : D × ℤ) (f : moduleCompactGenerators A D p ⟶ X),
    L.map f ≫ r = 0 → f ≫ map = 0

variable [L.CommShift ℤ] [L.IsTriangulated]
  [PreservesColimit (Discrete.functor (brownRelationFamily A D E L r)) L]

/-- 三角形の補完とL像のHom完全性から、関係を消す後続段階が存在する。 -/
lemma brownSuccessor_nonempty : Nonempty (BrownSuccessor A D E L r) := by
  obtain ⟨Z, a, b, hT⟩ := distinguished_cocone_triangle (brownRelationMap A D E L r)
  let T := Triangle.mk (brownRelationMap A D E L r) a b
  have hL := L.map_distinguished T hT
  obtain ⟨r', hr'⟩ := (L.mapTriangle.obj T).yoneda_exact₂ hL r
    (brownRelationMap_image_zero A D E L r)
  refine ⟨⟨Z, a, r', hr'.symm, ?_⟩⟩
  intro p f hf
  exact brownRelationMap_kills A D E L r a (comp_distTriang_mor_zero₁₂ T hT) p f hf

/-- 証明付きの後続操作を一つ選ぶ。 -/
def brownSuccessor : BrownSuccessor A D E L r :=
  Classical.choice (brownSuccessor_nonempty A D E L r)

/-- 後続操作は元の標的射を延長する。 -/
lemma brownSuccessor_fac :
    L.map (brownSuccessor A D E L r).map ≫ (brownSuccessor A D E L r).target = r :=
  (brownSuccessor A D E L r).fac

/-- 後続操作は、元の標的射の下で零になる生成元からの任意射を消す。 -/
lemma brownSuccessor_kills (p : D × ℤ) (f : moduleCompactGenerators A D p ⟶ X)
    (hf : L.map f ≫ r = 0) : f ≫ (brownSuccessor A D E L r).map = 0 :=
  (brownSuccessor A D E L r).kills p f hf

end SerrePositivity.DifferentialGraded.Morita
