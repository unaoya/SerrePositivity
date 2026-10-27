module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeClosedComparison
public import SerrePositivity.KST.SConstruction.DGPerfectModuleUnderlying

/-!
概要：同じ元閉比較の小包絡への持ち上げを元実加群射へ回収する。
方針：二つの充満包含の全 Hom 恒等作用を使う。
規約：元閉射の厳密等式を保持する。
使われ方：元実逆回転の小模型と実 realization 全比較の同じ入力照合。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  (J : Type w) (X : J → PerfectDGModule R E) {P : Type z} [DGCategory R P]
  (F G : DGFunctor R P (PerfectDGModule R E)) (i j : P → J)
  (hF : ∀ a, X (i a) = F.obj a) (hG : ∀ a, X (j a) = G.obj a)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x).val ⟶
    ForgetEnrichment.of (Complex R) (G.obj x).val)

/-- 概要：元比較の小包絡持ち上げの実像は同じ元実加群射。
方針：二つの包含の元 Hom 恒等作用を消去する。
規約：同じ閉射の厳密回収。使われ方：実逆回転小模型の指定比較入力。 -/
lemma dgSmallPerfectEnvelopeComparisonMap_module (x : P) :
    (dgPerfectModuleUnderlying R E (dgSmallPerfectEnvelopeInclusion R E J X)).onClosed.map
      (dgSmallPerfectEnvelopeComparisonMap R E J X F G i j hF hG a x) = a x := by
  change ForgetEnrichment.homTo (Complex R) (a x) ≫ (𝟙 _ ≫ 𝟙 _) =
    ForgetEnrichment.homTo (Complex R) (a x)
  simp only [Category.id_comp, Category.comp_id]
end SerrePositivity.KST.SConstruction
