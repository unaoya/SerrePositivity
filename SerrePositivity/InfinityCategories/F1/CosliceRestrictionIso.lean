module

public import SerrePositivity.InfinityCategories.F1.CosliceRestriction
public import SerrePositivity.InfinityCategories.F1.JoinLeftGluing
public import SerrePositivity.InfinityCategories.F1.TriangleLongEdge

/-!
概要：図式の同型表示を通じた相対 coslice 制限の充填性。
方針：同型による制限を次数ごとに同型と示し、相対比較の合成則を使う。
規約：Core の部分複体による制限と標準単体の面写像を同一の一般形へ移す。
使われ方：Kerodon Proposition 5.2.5.1、三角形から長辺への相対制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：図式の同型に沿う coslice 制限は同型。
方針：逆射による錐の前合成が各次数で逆写像になることを示す。
規約：f の IsIso インスタンスを使う。
使われ方：Kerodon §4.3.6、Proposition 5.2.5.1 の標準単体による表示。 -/
instance sliceUnderRestrict_isIso {K L X : SSet.{u}} (p : K ⟶ X)
    (f : L ⟶ K) [IsIso f] : IsIso (sliceUnderRestrict p f) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro n
  apply (isIso_iff_bijective _).2
  constructor
  · intro σ τ h
    apply Subtype.ext
    have hh := congrArg (fun z ↦ joinMap (inv f) (𝟙 _) ≫ z.val) h
    change joinMap (inv f) (𝟙 _) ≫ (joinMap f (𝟙 _) ≫ σ.val) =
      joinMap (inv f) (𝟙 _) ≫ (joinMap f (𝟙 _) ≫ τ.val) at hh
    simpa only [← Category.assoc, ← joinMap_comp, IsIso.inv_hom_id,
      Category.comp_id, joinMap_id, Category.id_comp] using hh
  · intro τ
    refine ⟨⟨joinMap (inv f) (𝟙 _) ≫ τ.val, ?_⟩, ?_⟩
    · rw [← Category.assoc, joinInl_joinMap, Category.assoc, τ.property]
      simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    · apply Subtype.ext
      change joinMap f (𝟙 _) ≫ (joinMap (inv f) (𝟙 _) ≫ τ.val) = τ.val
      simp only [← Category.assoc, ← joinMap_comp, IsIso.hom_inv_id,
        Category.comp_id, joinMap_id, Category.id_comp]

/-- 概要：横の二射が同型である可換四角形の相対比較写像は同型。
方針：四角形を pullback とし、その標準 pullback との比較同型を使う。
規約：縦の二射には仮定を置かない。
使われ方：Kerodon §4.3.6、相対 coslice 制限の同型表示の変更。 -/
instance squareComparison_isIso {E F B C : SSet.{u}} {f : E ⟶ F} {p : E ⟶ B}
    {q : F ⟶ C} {g : B ⟶ C} (sq : CommSq f p q g) [IsIso f] [IsIso g] :
    IsIso (squareComparison sq) := by
  let h := IsPullback.of_horiz_isIso sq
  change IsIso h.isoPullback.hom
  infer_instance

/-- 概要：図式の同型に沿う相対 coslice 制限は同型。
方針：上と底の制限が同型なので可換四角形の比較同型を使う。
規約：標的への射 q は任意。
使われ方：Kerodon §4.3.6、相対 coslice 制限の表示の同型不変性。 -/
instance relativeCosliceRestriction_isIso {K L X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) (f : L ⟶ K) [IsIso f] :
    IsIso (relativeCosliceRestriction p q f) :=
  squareComparison_isIso (cosliceRestrictionSquare p q f)

/-- 概要：部分複体の相対制限の充填性をその同型表示に移す。
方針：部分複体への制限と表示同型への制限を合成する。
規約：表示同型 e の始域 L は任意。
使われ方：Kerodon Proposition 5.2.5.1、面の標準単体表示への移行。 -/
lemma relativeCosliceRestriction_trivialKanFibration_subcomplexIso {K L X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) (K₀ : K.Subcomplex) (e : L ≅ (K₀ : SSet.{u}))
    [TrivialKanFibration (relativeCosliceMap p q K₀)] :
    TrivialKanFibration (relativeCosliceRestriction p q (e.hom ≫ K₀.ι)) := by
  have : TrivialKanFibration (relativeCosliceRestriction p q K₀.ι) :=
    (inferInstance : TrivialKanFibration (relativeCosliceMap p q K₀))
  exact relativeCosliceRestriction_trivialKanFibration_comp p q K₀.ι e.hom

/-- 概要：inner fibration の相対 coslice の長辺への制限は trivial Kan fibration。
方針：長辺の部分複体包含の右 anodyne 性と標準単体表示を使う。
規約：長辺は δ₁ : Δ[1] → Δ[2]。
使われ方：Kerodon Proposition 5.2.5.1、合成辺の cocartesian 性の消去。 -/
lemma relativeCosliceRestriction_triangleLongEdge {X Y : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [InnerFibration q] :
    TrivialKanFibration (relativeCosliceRestriction t q (stdSimplex.δ (1 : Fin 3))) := by
  have := relativeCosliceMap_trivialKanFibration_of_rightAnodyne t q
    (stdSimplex.face {(1 : Fin 3)}ᶜ) triangleLongFace_rightAnodyne
  have h := relativeCosliceRestriction_trivialKanFibration_subcomplexIso t q
    (stdSimplex.face {(1 : Fin 3)}ᶜ) (stdSimplex.faceSingletonComplIso (1 : Fin 3))
  simpa only [stdSimplex.faceSingletonComplIso_hom_ι] using h

end SerrePositivity.InfinityCategories
