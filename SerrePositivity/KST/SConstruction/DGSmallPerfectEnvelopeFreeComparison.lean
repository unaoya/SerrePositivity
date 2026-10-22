module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeExtension
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeZero
public import SerrePositivity.KST.SConstruction.DGGeneratorImagePerfect

/-! # 小模型の元の実延長による自由代表の比較と像生成
概要：元の graph 延長の自由代表比較を、同じ実像を含む小模型へ持ち上げる。
方針：D の元の代表延長同型と、全 Hom を保つ包含の閉零充満忠実性を使う。
規約：代表の延長像を選び直さない。使われ方：実 LT 入力の左対角像の生成条件。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (J : Type z) [Small.{u} J] (X : J → PerfectDGModule R D) (F : DGFunctor R D E)
local notation "C" => DGSmallPerfectEnvelope R D J X
local notation "Y" => dgSmallPerfectEnvelopeExtensionFamily R D E J X F
local notation "T" => DGSmallPerfectEnvelopeExtensionTarget R D E J X F
local notation "I" => dgSmallPerfectEnvelopeInclusion R E (C) (Y)
local notation "G" => dgSmallPerfectEnvelopeExtension R D E J X F
local instance : (I).onClosed.Full :=
  (I).onClosed_full_of_homIso (fun _ _ => by change IsIso (𝟙 _); infer_instance)
local instance : (I).onClosed.Faithful :=
  (I).onClosed_faithful_of_homIso (fun _ _ => by change IsIso (𝟙 _); infer_instance)
local instance : (perfectDGModuleInclusion R E Set.univ).onClosed.Full := by
  dsimp [perfectDGModuleInclusion]; infer_instance
local instance : (perfectDGModuleInclusion R E Set.univ).onClosed.Faithful := by
  dsimp [perfectDGModuleInclusion]; infer_instance

/-- 元の自由代表の実延長像は、同じ小模型内の元の自由代表と閉零で同型。 -/
def dgSmallPerfectEnvelopeExtensionRepresentableIso (d : D) :
    ForgetEnrichment.of (Complex R)
      ((G).obj (dgSmallPerfectEnvelopeRepresentable R D J X d)) ≅
    ForgetEnrichment.of (Complex R)
      (dgSmallPerfectEnvelopeRepresentable R E (C) (Y) (F.obj d)) := by
  apply (I).onClosed.preimageIso
  apply (perfectDGModuleInclusion R E Set.univ).onClosed.preimageIso
  exact dgModuleExtensionRepresentableIso R D E F d

/-- 同じ終域の自由代表が生成すれば、元の実延長の対象像が同じ全 Perf を生成する。 -/
lemma dgSmallPerfectEnvelopeExtension_perfectOver_image_eq (d : D)
    (hgen : modulePerfectOver R (T)
      {dgSmallPerfectEnvelopeRepresentable R E (C) (Y) (F.obj d)} = modulePerfect R (T)) :
    modulePerfectOver R (T) (Set.range (G).obj) = modulePerfect R (T) :=
  dgPerfectOver_image_eq_of_generator_iso R (T) (G)
    (dgSmallPerfectEnvelopeRepresentable R D J X d)
    (dgSmallPerfectEnvelopeRepresentable R E (C) (Y) (F.obj d)) hgen
    ((toHomotopy R (T)).mapIso
      (dgSmallPerfectEnvelopeExtensionRepresentableIso R D E J X F d))

end SerrePositivity.KST.SConstruction
