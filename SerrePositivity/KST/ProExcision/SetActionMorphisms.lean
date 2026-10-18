module
public import SerrePositivity.KST.ProExcision.SetActionBar
public import SerrePositivity.KST.ProExcision.ActionNerveCoordinates

/-!
# 単体的集合への作用の同変射

概要：作用するモノイドも動く同変射を作用 bar へ送る。
方針：各次数の作用圏の同変な誘導関手を組み立てる。
規約：KST Proposition A.1 の自然性と二重単体的な行の構成。
使われ方：離散群の作用 bar を単体次数について束ねる。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
variable {G G' G'' : SimplicialObject MonCat.{u}} {X X' X'' : SSet.{u}}

/-- 概要：作用するモノイドも含めた単体的集合の同変射。
方針：二つの単体的射と作用の可換条件を保持する。
規約：KST Proposition A.1 の数学的な入力であり、証明の結論を仮定しない。
使われ方：作用圏と作用 bar の誘導写像。 -/
structure SimplicialSetActionHom (A : SimplicialSetAction G X)
    (B : SimplicialSetAction G' X') where
  base : G ⟶ G'
  hom : X ⟶ X'
  equivariant (n : SimplexCategoryᵒᵖ) (a : G.obj n) (x : X.obj n) :
    hom.app n (A.action n a x) = B.action n (base.app n a) (hom.app n x)

/-- 概要：単体的な同変射は作用圏の単体的射を誘導する。
方針：対象と射ラベルの自然性を別々に検証する。
規約：KST Proposition A.1。使われ方：二重作用 bar の自然性。 -/
def simplicialSetActionCategoryMap {A : SimplicialSetAction G X}
    {B : SimplicialSetAction G' X'} (f : SimplicialSetActionHom A B) :
    simplicialSetActionCategory A ⟶ simplicialSetActionCategory B where
  app n := by
    letI := A.actionStructure n
    letI := B.actionStructure n
    exact (actionCategoryMap (f.base.app n).hom (f.hom.app n) (f.equivariant n)).toCatHom
  naturality n m φ := by
    letI := A.actionStructure n
    letI := A.actionStructure m
    letI := B.actionStructure n
    letI := B.actionStructure m
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun x ↦ ?_) ?_
    · apply ActionObject.ext
      exact congrArg (fun a ↦ a x.val) (f.hom.naturality φ)
    · intro x y a
      apply Subtype.ext
      dsimp [simplicialSetActionCategory, actionCategoryMap]
      simp only [actionObject_comp_val, actionObject_eqToHom_val, mul_one, one_mul]
      exact congrArg (fun b ↦ b.hom a.val) (f.base.naturality φ)

/-- 概要：同変射が誘導する作用 bar の射。
方針：作用圏の自然変換を nerve と対角へ送る。
規約：KST Proposition A.1 の自然性。
使われ方：係数の射と単体次数を動かす比較。 -/
def setActionBarMap {A : SimplicialSetAction G X} {B : SimplicialSetAction G' X'}
    (f : SimplicialSetActionHom A B) : setActionBar A ⟶ setActionBar B :=
  Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ)
    (Functor.uncurry.map (Functor.whiskerRight (simplicialSetActionCategoryMap f) nerveFunctor))

/-- 概要：同変な恒等射。
方針：両成分の恒等写像。
規約：KST Proposition A.1。使われ方：作用 bar の恒等則。 -/
def SimplicialSetActionHom.id (A : SimplicialSetAction G X) : SimplicialSetActionHom A A where
  base := 𝟙 _
  hom := 𝟙 _
  equivariant _ _ _ := rfl

/-- 概要：同変な単体的射の合成。
方針：二つの同変条件を順に適用する。
規約：KST Proposition A.1。使われ方：作用 bar の合成則。 -/
def SimplicialSetActionHom.comp {A : SimplicialSetAction G X}
    {B : SimplicialSetAction G' X'} {C : SimplicialSetAction G'' X''}
    (f : SimplicialSetActionHom A B) (g : SimplicialSetActionHom B C) :
    SimplicialSetActionHom A C where
  base := f.base ≫ g.base
  hom := f.hom ≫ g.hom
  equivariant n a x := by
    change g.hom.app n (f.hom.app n (A.action n a x)) = _
    rw [f.equivariant, g.equivariant]
    rfl

/-- 概要：作用 bar の誘導射は恒等射を保つ。
方針：作用圏・nerve・対角の恒等射保存を評価する。
規約：KST Proposition A.1。使われ方：単体的な作用 bar の束ね直し。 -/
@[simp] lemma setActionBarMap_id (A : SimplicialSetAction G X) :
    setActionBarMap (SimplicialSetActionHom.id A) = 𝟙 _ := by
  rfl

/-- 概要：作用 bar の誘導射は合成を保つ。
方針：対象と射のラベルの合成は定義通り一致する。
規約：KST Proposition A.1。使われ方：二重単体的な係数作用 bar の合成則。 -/
lemma setActionBarMap_comp {A : SimplicialSetAction G X}
    {B : SimplicialSetAction G' X'} {C : SimplicialSetAction G'' X''}
    (f : SimplicialSetActionHom A B) (g : SimplicialSetActionHom B C) :
    setActionBarMap (f.comp g) = setActionBarMap f ≫ setActionBarMap g := by
  rfl

end SerrePositivity.KST.ProExcision
