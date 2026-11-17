module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalAdjoints
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.CategoryTheory.EqToHom

/-!
概要：walking adjunction の混合Homに用いる端点保存の単体圏を構成する。
方針：単体圏の広部分圏とし、実際の有限順序射のGalois随伴で反変対応を作る。
規約：最小元・最大元の保存を混同せず、同じ有限順序集合上の射を使う。
使われ方：HA Proposition 4.7.3.3 の全拡張の添字、Riehl–Verity Observation 3.3.6・
Remark 3.3.8 の混合Hom。Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：単体圏の射が最小元を保つという条件。
方針：元の有限単調射を0で評価する。規約：次数0の単体も含む。
使われ方：Riehl–Verity Observation 3.3.6 のΔ−∞。 -/
def simplexPreservesBottom : MorphismProperty SimplexCategory :=
  fun _ _ f => f.toOrderHom 0 = 0

/-- 概要：最小元の保存は恒等射と合成で保たれる。
方針：合成を0で評価する。規約：同じ単体圏の射。
使われ方：Riehl–Verity Observation 3.3.6 の実部分圏。 -/
instance simplexPreservesBottom_multiplicative : simplexPreservesBottom.IsMultiplicative where
  id_mem _ := rfl
  comp_mem f g hf hg := by
    change g.toOrderHom (f.toOrderHom 0) = 0
    rw [hf, hg]

/-- 概要：単体圏の射が最大元を保つという条件。
方針：指定された最後の元で評価する。規約：始域と値域の最後の元を使い分ける。
使われ方：Riehl–Verity Observation 3.3.6 のΔ∞。 -/
def simplexPreservesTop : MorphismProperty SimplexCategory :=
  fun x y f => f.toOrderHom (Fin.last x.len) = Fin.last y.len

/-- 概要：最大元の保存は恒等射と合成で保たれる。
方針：合成を最後の元で計算する。規約：任意の単体圏の合成。
使われ方：Riehl–Verity Observation 3.3.6 のΔ∞の圏構造。 -/
instance simplexPreservesTop_multiplicative : simplexPreservesTop.IsMultiplicative where
  id_mem _ := rfl
  comp_mem f g hf hg := by
    change g.toOrderHom (f.toOrderHom _) = _
    rw [hf, hg]

/-- 概要：最小元を保つ有限順序射の実圏。
方針：広部分圏の既存の圏構造を使う。規約：対象は元の全ての非空有限順序集合。
使われ方：Riehl–Verity Remark 3.3.8 のAdj(+,−)。 -/
abbrev BottomSimplexCategory := WideSubcategory simplexPreservesBottom

/-- 概要：最大元を保つ有限順序射の実圏。
方針：広部分圏を使う。規約：対象の次数を変えない。
使われ方：Riehl–Verity Remark 3.3.8 のAdj(−,+)。 -/
abbrev TopSimplexCategory := WideSubcategory simplexPreservesTop

/-- 概要：最小元を保つ射の右随伴を、逆向きの最大元を保つ射にする。
方針：証明済みの有限Galois随伴を包む。規約：同じ二つの順序集合を使う。
使われ方：Riehl–Verity Observation 3.3.6 の反変対応。 -/
def bottomSimplexRightAdjoint {X Y : BottomSimplexCategory} (f : X ⟶ Y) :
    (⟨Y.obj⟩ : TopSimplexCategory) ⟶ ⟨X.obj⟩ :=
  ⟨SimplexCategory.Hom.mk (ordinalRightAdjoint f.hom.toOrderHom f.property),
    ordinalRightAdjoint_last f.hom.toOrderHom f.property⟩

/-- 概要：最大元を保つ射の左随伴を、逆向きの最小元を保つ射にする。
方針：実際の左随伴の構成を使う。規約：底の有限順序集合はそのまま。
使われ方：Riehl–Verity Observation 3.3.6 の逆の反変対応。 -/
def topSimplexLeftAdjoint {X Y : TopSimplexCategory} (g : X ⟶ Y) :
    (⟨Y.obj⟩ : BottomSimplexCategory) ⟶ ⟨X.obj⟩ :=
  ⟨SimplexCategory.Hom.mk (ordinalLeftAdjoint g.hom.toOrderHom g.property),
    ordinalLeftAdjoint_zero g.hom.toOrderHom g.property⟩

/-- 概要：最小元保存の圏から最大元保存の圏の反対への実関手。
方針：実右随伴を取り、随伴の一意性で恒等射と合成を照合する。
規約：対象の次数は保つ。使われ方：Riehl–Verity Observation 3.3.6。 -/
def bottomSimplexToTopOp : BottomSimplexCategory ⥤ TopSimplexCategoryᵒᵖ where
  obj X := op ⟨X.obj⟩
  map f := (bottomSimplexRightAdjoint f).op
  map_id X := by
    apply Quiver.Hom.unop_inj
    apply WideSubcategory.hom_ext
    apply SimplexCategory.Hom.ext'
    exact ordinalRightAdjoint_id X.obj.len
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply WideSubcategory.hom_ext
    apply SimplexCategory.Hom.ext'
    exact ordinalRightAdjoint_comp f.hom.toOrderHom g.hom.toOrderHom f.property g.property

/-- 概要：最大元保存の圏の反対から最小元保存の圏への逆の実関手。
方針：実左随伴を取り、その合成則を使う。
規約：元の有限順序集合を変えない。使われ方：Riehl–Verity Observation 3.3.6。 -/
def topOpSimplexToBottom : TopSimplexCategoryᵒᵖ ⥤ BottomSimplexCategory where
  obj X := ⟨X.unop.obj⟩
  map f := topSimplexLeftAdjoint f.unop
  map_id X := by
    apply WideSubcategory.hom_ext
    apply SimplexCategory.Hom.ext'
    exact ordinalLeftAdjoint_id X.unop.obj.len
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply SimplexCategory.Hom.ext'
    exact ordinalLeftAdjoint_comp f.unop.hom.toOrderHom g.unop.hom.toOrderHom
      f.unop.property g.unop.property

/-- 概要：右随伴と左随伴の往復の関手は最小元保存の圏の恒等関手に等しい。
方針：対象は同じで、各射のGalois随伴の相互逆性を使う。
規約：自然同型に弱めない関手の等式。使われ方：Riehl–Verity Observation 3.3.6。 -/
lemma bottomSimplex_roundtrip : bottomSimplexToTopOp ⋙ topOpSimplexToBottom =
    𝟭 BottomSimplexCategory := by
  refine CategoryTheory.Functor.ext (F := bottomSimplexToTopOp ⋙ topOpSimplexToBottom)
    (G := 𝟭 BottomSimplexCategory) (fun X => by cases X; rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply WideSubcategory.hom_ext
  apply SimplexCategory.Hom.ext'
  exact ordinal_left_right f.hom.toOrderHom f.property

/-- 概要：左随伴と右随伴の往復の関手は最大元保存の反対圏の恒等関手に等しい。
方針：反対を外し、射ごとのGalois随伴の相互逆性を使う。
規約：元の全関手の等式。使われ方：Riehl–Verity Observation 3.3.6。 -/
lemma topSimplex_roundtrip : topOpSimplexToBottom ⋙ bottomSimplexToTopOp =
    𝟭 TopSimplexCategoryᵒᵖ := by
  refine CategoryTheory.Functor.ext (F := topOpSimplexToBottom ⋙ bottomSimplexToTopOp)
    (G := 𝟭 TopSimplexCategoryᵒᵖ) (fun X => by cases X; rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Quiver.Hom.unop_inj
  apply WideSubcategory.hom_ext
  apply SimplexCategory.Hom.ext'
  exact ordinal_right_left f.unop.hom.toOrderHom f.unop.property

/-- 概要：最小元保存の単体圏と最大元保存の反対圏の実同値。
方針：相互逆の二つの実関手と、関手の等式を使う。
規約：walking adjunctionの混合Homの同定。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Observation 3.3.6・Remark 3.3.8。 -/
def endpointSimplexEquivalence : BottomSimplexCategory ≌ TopSimplexCategoryᵒᵖ where
  functor := bottomSimplexToTopOp
  inverse := topOpSimplexToBottom
  unitIso := eqToIso bottomSimplex_roundtrip.symm
  counitIso := eqToIso topSimplex_roundtrip

end SerrePositivity.InfinityCategories.HA.Monads
