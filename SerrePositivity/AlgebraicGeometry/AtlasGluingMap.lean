module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
概要：元の開被覆の重なりの Cartesian な模型から、貼り合わせへの実際の射を作る。
方針：局所射を貼り合わせ、二重交叉の Cartesian 性から各チャートの逆像を同定する。
規約：重なりの模型の存在は別工程。元の開被覆を保つ比較の法則。
使われ方：G2 の一般の有限表示対象と模型の底変換との比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable (D : Scheme.GlueData.{u}) {X : Scheme.{u}}
  (U : D.J → Scheme.{u}) (j : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (j i)]
  (hcover : ∀ x : X, ∃ i z, j i z = x)
  (a : ∀ i, U i ⟶ D.U i)
  (b : ∀ i k, pullback (j i) (j k) ⟶ D.V (i, k))
  (hb : ∀ i k, IsPullback (b i k) (pullback.fst (j i) (j k)) (D.f i k) (a i))
  (hcompat : ∀ i k, b i k ≫ D.t i k ≫ D.f k i = pullback.snd (j i) (j k) ≫ a k)

/-- 元の開被覆を、glue data と同じ添字で保持する。 -/
def gluingAtlasCover (D : Scheme.GlueData.{u}) {X : Scheme.{u}}
    (U : D.J → Scheme.{u}) (j : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x : X, ∃ i z, j i z = x) : X.OpenCover where
  I₀ := D.J
  X := U
  f := j
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨hcover, inferInstance⟩

include b hb hcompat

/-- 二重交叉の模型の可換式から、局所比較の貼り合わせ条件が得られる。 -/
theorem gluingAtlasMap_compat (i k : D.J) :
    pullback.fst (j i) (j k) ≫ a i ≫ D.ι i =
      pullback.snd (j i) (j k) ≫ a k ≫ D.ι k := by
  calc
    _ = b i k ≫ D.f i k ≫ D.ι i := ((hb i k).w_assoc (D.ι i)).symm
    _ = b i k ≫ D.t i k ≫ D.f k i ≫ D.ι k := by
      rw [D.glue_condition]
    _ = _ := by simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ D.ι k) (hcompat i k)

include hcover

/-- 元の各チャートの比較を、実際の貼り合わせへの射にする。 -/
def gluingAtlasMap : X ⟶ D.glued :=
  (gluingAtlasCover D U j hcover).glueMorphisms (fun i ↦ a i ≫ D.ι i)
    (gluingAtlasMap_compat D U j a b hb hcompat)

/-- 貼り合わせへの射は、元の各開で指定した局所射に一致する。 -/
@[reassoc] theorem gluingAtlasMap_ι (i : D.J) :
    j i ≫ gluingAtlasMap D U j hcover a b hb hcompat = a i ≫ D.ι i :=
  (gluingAtlasCover D U j hcover).ι_glueMorphisms
    (fun i ↦ a i ≫ D.ι i) (gluingAtlasMap_compat D U j a b hb hcompat) i

/-- 模型のチャートの逆像は、元の同じチャートの像そのもの。 -/
theorem gluingAtlasMap_preimage_range (i : D.J) :
    (gluingAtlasMap D U j hcover a b hb hcompat) ⁻¹' Set.range (D.ι i) = Set.range (j i) := by
  ext x
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨k, z, rfl⟩ := hcover x
    have hmap : gluingAtlasMap D U j hcover a b hb hcompat (j k z) = D.ι k (a k z) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun q : U k ⟶ D.glued ↦ q z) (gluingAtlasMap_ι D U j hcover a b hb hcompat k)
    have heq : D.ι k (a k z) = D.ι i v := hmap.symm.trans hv.symm
    obtain ⟨w, hw, _⟩ := (D.ι_eq_iff k i (a k z) v).mp heq
    obtain ⟨o, _, ho⟩ := Scheme.exists_preimage_of_isPullback (hb k i) w z hw
    refine ⟨pullback.snd (j k) (j i) o, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, ho]
  · rintro ⟨z, rfl⟩
    refine ⟨a i z, ?_⟩
    symm
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun q : U i ⟶ D.glued ↦ q z) (gluingAtlasMap_ι D U j hcover a b hb hcompat i)

/-- 開部分としても、模型のチャートの逆像は元の同じチャート。 -/
theorem gluingAtlasMap_preimage_opensRange (i : D.J) :
    gluingAtlasMap D U j hcover a b hb hcompat ⁻¹ᵁ (D.ι i).opensRange = (j i).opensRange :=
  TopologicalSpace.Opens.coe_inj.mp (gluingAtlasMap_preimage_range D U j hcover a b hb hcompat i)

/-- 各元の開包含と模型のチャートの正方形は Cartesian。 -/
theorem isPullback_gluingAtlasMap_chart (i : D.J) :
    IsPullback (a i) (j i) (D.ι i) (gluingAtlasMap D U j hcover a b hb hcompat) :=
  IsOpenImmersion.isPullback _ _ _ _ (gluingAtlasMap_ι D U j hcover a b hb hcompat i)
    (gluingAtlasMap_preimage_opensRange D U j hcover a b hb hcompat i)

end SerrePositivity.AlgebraicGeometry
