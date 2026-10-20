import SerrePositivity.KST.SConstruction

/-!
概要：S• 構成の公開宣言の型と公理を監査する。
方針：型の検査と公理一覧を各宣言について出力する。
規約：propext・Classical.choice・Quot.sound のみ許可。
使われ方：BGT §7 に対応する保存単位の検証。
-/

#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion
#check @SerrePositivity.KST.SConstruction.arCofiberCompletion
#print axioms SerrePositivity.KST.SConstruction.arCofiberCompletion
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_boundary
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_boundary
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.pointFamily
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.pointFamily
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.pointFamily_isCofiber
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.pointFamily_isCofiber
#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator
#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_vertex
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_vertex
#check @SerrePositivity.KST.SConstruction.IsGapped.arCofiberFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.IsGapped.arCofiberFamily_vertex
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_ι
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_ι
#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_apex
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_apex
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_apex
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_apex
#check @SerrePositivity.KST.SConstruction.intervalStep_mono_endpoints
#print axioms SerrePositivity.KST.SConstruction.intervalStep_mono_endpoints
#check @SerrePositivity.KST.SConstruction.arCofiberSquareOrder
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareOrder
#check @SerrePositivity.KST.SConstruction.arCofiberSquareChain
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareChain
#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap
#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_at
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_at
#check @SerrePositivity.KST.SConstruction.curry_vertex_value
#print axioms SerrePositivity.KST.SConstruction.curry_vertex_value
#check @SerrePositivity.KST.SConstruction.arCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamily
#check @SerrePositivity.KST.SConstruction.arCofiberFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamily_vertex
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamily
#check @SerrePositivity.KST.SConstruction.curry_evaluate_vertex
#print axioms SerrePositivity.KST.SConstruction.curry_evaluate_vertex
#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_apex
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_apex
#check @SerrePositivity.KST.SConstruction.arCofiberFamily_apex
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamily_apex
#check @SerrePositivity.KST.SConstruction.cofiberApex
#print axioms SerrePositivity.KST.SConstruction.cofiberApex
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamily_apex
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamily_apex
#check @SerrePositivity.KST.SConstruction.arCofiberInputOrder
#print axioms SerrePositivity.KST.SConstruction.arCofiberInputOrder
#check @SerrePositivity.KST.SConstruction.arCofiberInputMap
#print axioms SerrePositivity.KST.SConstruction.arCofiberInputMap
#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_bottom
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_bottom
#check @SerrePositivity.KST.SConstruction.frameCofiberInputOperator
#print axioms SerrePositivity.KST.SConstruction.frameCofiberInputOperator
#check @SerrePositivity.KST.SConstruction.frameCofiberInputs
#print axioms SerrePositivity.KST.SConstruction.frameCofiberInputs
#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_input
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_input
#check @SerrePositivity.KST.SConstruction.gappedFrameRestriction_ι
#print axioms SerrePositivity.KST.SConstruction.gappedFrameRestriction_ι
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_input
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_input
#check @SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex
#print axioms SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex
#check @SerrePositivity.KST.SConstruction.cofiberDiagrams
#print axioms SerrePositivity.KST.SConstruction.cofiberDiagrams
#check @SerrePositivity.KST.SConstruction.cofiberProjection
#print axioms SerrePositivity.KST.SConstruction.cofiberProjection
#check @SerrePositivity.KST.SConstruction.cofiberForgetZero
#print axioms SerrePositivity.KST.SConstruction.cofiberForgetZero
#check @SerrePositivity.KST.SConstruction.cofiberForgetZero_ι
#print axioms SerrePositivity.KST.SConstruction.cofiberForgetZero_ι
#check @SerrePositivity.KST.SConstruction.cofiberZeroArrow
#print axioms SerrePositivity.KST.SConstruction.cofiberZeroArrow
#check @SerrePositivity.KST.SConstruction.cofiberZeroArrow_ι
#print axioms SerrePositivity.KST.SConstruction.cofiberZeroArrow_ι
#check @SerrePositivity.KST.SConstruction.cofiberZeroArrow_source
#print axioms SerrePositivity.KST.SConstruction.cofiberZeroArrow_source
#check @SerrePositivity.KST.SConstruction.pushoutProjection_bottom
#print axioms SerrePositivity.KST.SConstruction.pushoutProjection_bottom
#check @SerrePositivity.KST.SConstruction.cofiberProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.cofiberProjection_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.exists_relative_cofiberFamily
#print axioms SerrePositivity.KST.SConstruction.exists_relative_cofiberFamily
#check @SerrePositivity.KST.SConstruction.cofiberFamilySpace
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySpace
#check @SerrePositivity.KST.SConstruction.cofiberFamilySpace_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySpace_isContractibleKan
#check @SerrePositivity.KST.SConstruction.cofiberFamiliesIso
#print axioms SerrePositivity.KST.SConstruction.cofiberFamiliesIso
#check @SerrePositivity.KST.SConstruction.cofiberSection
#print axioms SerrePositivity.KST.SConstruction.cofiberSection
#check @SerrePositivity.KST.SConstruction.cofiberSection_projection
#print axioms SerrePositivity.KST.SConstruction.cofiberSection_projection
#check @SerrePositivity.KST.SConstruction.cofiberFunctor
#print axioms SerrePositivity.KST.SConstruction.cofiberFunctor
#check @SerrePositivity.KST.SConstruction.arSquare_cofiber_zero_corner
#print axioms SerrePositivity.KST.SConstruction.arSquare_cofiber_zero_corner
#check @SerrePositivity.KST.SConstruction.gappedCofiberTriangle
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberTriangle
#check @SerrePositivity.KST.SConstruction.gappedCofiberTriangle_isCofiber
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberTriangle_isCofiber
#check @SerrePositivity.KST.SConstruction.firstRowNerve
#print axioms SerrePositivity.KST.SConstruction.firstRowNerve
#check @SerrePositivity.KST.SConstruction.firstRowOrder
#print axioms SerrePositivity.KST.SConstruction.firstRowOrder
#check @SerrePositivity.KST.SConstruction.firstRowInclusion
#print axioms SerrePositivity.KST.SConstruction.firstRowInclusion
#check @SerrePositivity.KST.SConstruction.firstRowRestriction
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction
#check @SerrePositivity.KST.SConstruction.gappedDiagram
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram
#check @SerrePositivity.KST.SConstruction.gappedDiagram_isGapped
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_isGapped
#check @SerrePositivity.KST.SConstruction.firstRowRestriction_vertex
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_vertex
#check @SerrePositivity.KST.SConstruction.firstRowSimplexIso
#print axioms SerrePositivity.KST.SConstruction.firstRowSimplexIso
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData
#check @SerrePositivity.KST.SConstruction.firstRowCofiberData
#print axioms SerrePositivity.KST.SConstruction.firstRowCofiberData
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_boundary
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_boundary
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_isGapped_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_isGapped_of_vertexSurjective
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_ι
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_ι
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_boundary
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_boundary
#check @SerrePositivity.KST.SConstruction.boundary_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.boundary_vertex_surjective
#check @SerrePositivity.KST.SConstruction.exists_gappedBoundaryFilling_of_firstRowFilling
#print axioms SerrePositivity.KST.SConstruction.exists_gappedBoundaryFilling_of_firstRowFilling
#check @SerrePositivity.KST.SConstruction.frame_extend_boundary
#print axioms SerrePositivity.KST.SConstruction.frame_extend_boundary
#check @SerrePositivity.KST.SConstruction.firstRowFrameOrder
#print axioms SerrePositivity.KST.SConstruction.firstRowFrameOrder
#check @SerrePositivity.KST.SConstruction.firstRowFrameMap
#print axioms SerrePositivity.KST.SConstruction.firstRowFrameMap
#check @SerrePositivity.KST.SConstruction.frameRowChain_positive
#print axioms SerrePositivity.KST.SConstruction.frameRowChain_positive
#check @SerrePositivity.KST.SConstruction.frameRowChainInverse
#print axioms SerrePositivity.KST.SConstruction.frameRowChainInverse
#check @SerrePositivity.KST.SConstruction.frameFirstRowMap
#print axioms SerrePositivity.KST.SConstruction.frameFirstRowMap
#check @SerrePositivity.KST.SConstruction.firstRowFrameMap_comp
#print axioms SerrePositivity.KST.SConstruction.firstRowFrameMap_comp
#check @SerrePositivity.KST.SConstruction.frameFirstRowMap_comp
#print axioms SerrePositivity.KST.SConstruction.frameFirstRowMap_comp
#check @SerrePositivity.KST.SConstruction.frameFirstRowIso
#print axioms SerrePositivity.KST.SConstruction.frameFirstRowIso
#check @SerrePositivity.KST.SConstruction.simplexFirstVertex_stdSimplex_of_notMem_boundary
#print axioms SerrePositivity.KST.SConstruction.simplexFirstVertex_stdSimplex_of_notMem_boundary
#check @SerrePositivity.KST.SConstruction.initialBoundaryLifting_ihom_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.initialBoundaryLifting_ihom_of_pointwise
#check @SerrePositivity.KST.SConstruction.isInitialVertex_functorVertex_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isInitialVertex_functorVertex_of_pointwise
#check @SerrePositivity.KST.SConstruction.isZeroVertex_functorVertex_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isZeroVertex_functorVertex_of_pointwise
#check @SerrePositivity.KST.SConstruction.isZeroVertex_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isZeroVertex_of_pointwise
#check @SerrePositivity.KST.SConstruction.evaluateFunctorCocone
#print axioms SerrePositivity.KST.SConstruction.evaluateFunctorCocone
#check @SerrePositivity.KST.SConstruction.IsPointwiseColimitCone
#print axioms SerrePositivity.KST.SConstruction.IsPointwiseColimitCone
#check @SerrePositivity.KST.SConstruction.initialBoundaryLifting_coconeRestriction_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.initialBoundaryLifting_coconeRestriction_of_pointwise
#check @SerrePositivity.KST.SConstruction.isColimitCone_of_pointwise_initialBoundaryLifting
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_of_pointwise_initialBoundaryLifting
#check @SerrePositivity.KST.SConstruction.isColimitCone_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_of_pointwise
#check @SerrePositivity.KST.SConstruction.isPushoutSquare_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_of_pointwise
#check @SerrePositivity.KST.SConstruction.Ar
#print axioms SerrePositivity.KST.SConstruction.Ar
#check @SerrePositivity.KST.SConstruction.arObj
#print axioms SerrePositivity.KST.SConstruction.arObj
#check @SerrePositivity.KST.SConstruction.arMap
#print axioms SerrePositivity.KST.SConstruction.arMap
#check @SerrePositivity.KST.SConstruction.arMap_id
#print axioms SerrePositivity.KST.SConstruction.arMap_id
#check @SerrePositivity.KST.SConstruction.arMap_comp
#print axioms SerrePositivity.KST.SConstruction.arMap_comp
#check @SerrePositivity.KST.SConstruction.arNerve
#print axioms SerrePositivity.KST.SConstruction.arNerve
#check @SerrePositivity.KST.SConstruction.arNerveMap
#print axioms SerrePositivity.KST.SConstruction.arNerveMap
#check @SerrePositivity.KST.SConstruction.arNerveMap_id
#print axioms SerrePositivity.KST.SConstruction.arNerveMap_id
#check @SerrePositivity.KST.SConstruction.arNerveMap_comp
#print axioms SerrePositivity.KST.SConstruction.arNerveMap_comp
#check @SerrePositivity.KST.SConstruction.diagramSpace
#print axioms SerrePositivity.KST.SConstruction.diagramSpace
#check @SerrePositivity.KST.SConstruction.intervalStep
#print axioms SerrePositivity.KST.SConstruction.intervalStep
#check @SerrePositivity.KST.SConstruction.intervalStep_le
#print axioms SerrePositivity.KST.SConstruction.intervalStep_le
#check @SerrePositivity.KST.SConstruction.le_intervalStep
#print axioms SerrePositivity.KST.SConstruction.le_intervalStep
#check @SerrePositivity.KST.SConstruction.arSquareOrder
#print axioms SerrePositivity.KST.SConstruction.arSquareOrder
#check @SerrePositivity.KST.SConstruction.arSquare
#print axioms SerrePositivity.KST.SConstruction.arSquare
#check @SerrePositivity.KST.SConstruction.IsGapped
#print axioms SerrePositivity.KST.SConstruction.IsGapped
#check @SerrePositivity.KST.SConstruction.arSquare_naturality
#print axioms SerrePositivity.KST.SConstruction.arSquare_naturality
#check @SerrePositivity.KST.SConstruction.IsGapped.precomp
#print axioms SerrePositivity.KST.SConstruction.IsGapped.precomp
#check @SerrePositivity.KST.SConstruction.gappedSubcomplex
#print axioms SerrePositivity.KST.SConstruction.gappedSubcomplex
#check @SerrePositivity.KST.SConstruction.sConstruction
#print axioms SerrePositivity.KST.SConstruction.sConstruction
#check @SerrePositivity.KST.SConstruction.sConstruction_quasicategory
#print axioms SerrePositivity.KST.SConstruction.sConstruction_quasicategory
#check @SerrePositivity.KST.SConstruction.sMap
#print axioms SerrePositivity.KST.SConstruction.sMap
#check @SerrePositivity.KST.SConstruction.sMap_ι
#print axioms SerrePositivity.KST.SConstruction.sMap_ι
#check @SerrePositivity.KST.SConstruction.sMap_id
#print axioms SerrePositivity.KST.SConstruction.sMap_id
#check @SerrePositivity.KST.SConstruction.sMap_comp
#print axioms SerrePositivity.KST.SConstruction.sMap_comp
#check @SerrePositivity.KST.SConstruction.simplicialSConstruction
#print axioms SerrePositivity.KST.SConstruction.simplicialSConstruction
#check @SerrePositivity.KST.SConstruction.frameInclusion
#print axioms SerrePositivity.KST.SConstruction.frameInclusion
#check @SerrePositivity.KST.SConstruction.firstRowFrameMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.firstRowFrameMap_inclusion
#check @SerrePositivity.KST.SConstruction.IsGapped.zeroFrameVertex
#print axioms SerrePositivity.KST.SConstruction.IsGapped.zeroFrameVertex
#check @SerrePositivity.KST.SConstruction.gappedFrameRestriction
#print axioms SerrePositivity.KST.SConstruction.gappedFrameRestriction
#check @SerrePositivity.KST.SConstruction.frameRowRestriction
#print axioms SerrePositivity.KST.SConstruction.frameRowRestriction
#check @SerrePositivity.KST.SConstruction.firstRowRestriction_factor
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_factor
#check @SerrePositivity.KST.SConstruction.frameRowDiagramIso
#print axioms SerrePositivity.KST.SConstruction.frameRowDiagramIso
#check @SerrePositivity.KST.SConstruction.frameRowRestriction_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.frameRowRestriction_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.initialBoundaryLifting_map_iso
#print axioms SerrePositivity.KST.SConstruction.initialBoundaryLifting_map_iso
#check @SerrePositivity.KST.SConstruction.internalHomFlipHomEquiv_evaluate
#print axioms SerrePositivity.KST.SConstruction.internalHomFlipHomEquiv_evaluate
#check @SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex.zero_evaluation
#print axioms SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex.zero_evaluation
#check @SerrePositivity.KST.SConstruction.cofiberFamilySquare
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySquare
#check @SerrePositivity.KST.SConstruction.cofiberFamilySquare_evaluate
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySquare_evaluate
#check @SerrePositivity.KST.SConstruction.cofiberFamilySquare_zero_corner
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySquare_zero_corner
#check @SerrePositivity.KST.SConstruction.cofiberFamilyTriangle
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyTriangle
#check @SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_isCofiber
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_isCofiber
#check @SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_apex
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_apex
#check @SerrePositivity.KST.SConstruction.IsPushoutDiagramVertex
#print axioms SerrePositivity.KST.SConstruction.IsPushoutDiagramVertex
#check @SerrePositivity.KST.SConstruction.pushoutDiagrams
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagrams
#check @SerrePositivity.KST.SConstruction.squareCoconeDiagramIso
#print axioms SerrePositivity.KST.SConstruction.squareCoconeDiagramIso
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso
#check @SerrePositivity.KST.SConstruction.pushoutProjection
#print axioms SerrePositivity.KST.SConstruction.pushoutProjection
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_projection
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_projection
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_inv_projection
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_inv_projection
#check @SerrePositivity.KST.SConstruction.exists_relative_pushoutFamily
#print axioms SerrePositivity.KST.SConstruction.exists_relative_pushoutFamily
#check @SerrePositivity.KST.SConstruction.pushoutProjection_hasLiftingProperty_boundary
#print axioms SerrePositivity.KST.SConstruction.pushoutProjection_hasLiftingProperty_boundary
#check @SerrePositivity.KST.SConstruction.exists_relative_colimitCoconeFamily
#print axioms SerrePositivity.KST.SConstruction.exists_relative_colimitCoconeFamily
#check @SerrePositivity.KST.SConstruction.colimitCoconeFamily_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.colimitCoconeFamily_relative_lifting
#check @SerrePositivity.KST.SConstruction.exists_lift_of_initial_first_vertices
#print axioms SerrePositivity.KST.SConstruction.exists_lift_of_initial_first_vertices
#check @SerrePositivity.KST.SConstruction.exists_extension_with_vertices
#print axioms SerrePositivity.KST.SConstruction.exists_extension_with_vertices
#check @SerrePositivity.KST.SConstruction.exists_extension_of_initial_or_terminal_endpoints
#print axioms SerrePositivity.KST.SConstruction.exists_extension_of_initial_or_terminal_endpoints
#check @SerrePositivity.KST.SConstruction.zeroChoices
#print axioms SerrePositivity.KST.SConstruction.zeroChoices
#check @SerrePositivity.KST.SConstruction.zeroChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.zeroChoices_isContractibleKan
#check @SerrePositivity.KST.SConstruction.zeroChoices_kanComplex
#print axioms SerrePositivity.KST.SConstruction.zeroChoices_kanComplex
#check @SerrePositivity.KST.SConstruction.exists_zeroChoices_extension
#print axioms SerrePositivity.KST.SConstruction.exists_zeroChoices_extension
#check @SerrePositivity.KST.SConstruction.IsDiagonal
#print axioms SerrePositivity.KST.SConstruction.IsDiagonal
#check @SerrePositivity.KST.SConstruction.IsPositiveRow
#print axioms SerrePositivity.KST.SConstruction.IsPositiveRow
#check @SerrePositivity.KST.SConstruction.positiveRow_orderConvex
#print axioms SerrePositivity.KST.SConstruction.positiveRow_orderConvex
#check @SerrePositivity.KST.SConstruction.positiveRow_of_frame_not_diagonal
#print axioms SerrePositivity.KST.SConstruction.positiveRow_of_frame_not_diagonal
#check @SerrePositivity.KST.SConstruction.frameChain_diagonal_endpoint
#print axioms SerrePositivity.KST.SConstruction.frameChain_diagonal_endpoint
#check @SerrePositivity.KST.SConstruction.FrameAr
#print axioms SerrePositivity.KST.SConstruction.FrameAr
#check @SerrePositivity.KST.SConstruction.frameForgetOrder
#print axioms SerrePositivity.KST.SConstruction.frameForgetOrder
#check @SerrePositivity.KST.SConstruction.frameNerve
#print axioms SerrePositivity.KST.SConstruction.frameNerve
#check @SerrePositivity.KST.SConstruction.framePositiveRow
#print axioms SerrePositivity.KST.SConstruction.framePositiveRow
#check @SerrePositivity.KST.SConstruction.frameNerve_diagonal_endpoint
#print axioms SerrePositivity.KST.SConstruction.frameNerve_diagonal_endpoint
#check @SerrePositivity.KST.SConstruction.zeroFrame_extend_boundary
#print axioms SerrePositivity.KST.SConstruction.zeroFrame_extend_boundary
#check @SerrePositivity.KST.SConstruction.IsZeroFrameVertex
#print axioms SerrePositivity.KST.SConstruction.IsZeroFrameVertex
#check @SerrePositivity.KST.SConstruction.zeroFrameDiagrams
#print axioms SerrePositivity.KST.SConstruction.zeroFrameDiagrams
#check @SerrePositivity.KST.SConstruction.zeroFrameProjection
#print axioms SerrePositivity.KST.SConstruction.zeroFrameProjection
#check @SerrePositivity.KST.SConstruction.diagonal_not_positiveRow
#print axioms SerrePositivity.KST.SConstruction.diagonal_not_positiveRow
#check @SerrePositivity.KST.SConstruction.diagonal_not_mem_framePositiveRow
#print axioms SerrePositivity.KST.SConstruction.diagonal_not_mem_framePositiveRow
#check @SerrePositivity.KST.SConstruction.exists_zeroFrame_extension
#print axioms SerrePositivity.KST.SConstruction.exists_zeroFrame_extension
#check @SerrePositivity.KST.SConstruction.zeroFrameProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.zeroFrameProjection_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.mk
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.mk
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.family
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.family
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.boundary
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.boundary
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.input
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.input
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.mk
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.mk
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.frame
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.frame
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.frame_boundary
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.frame_boundary
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.firstRow
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.firstRow
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.cofibers
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.cofibers

#check @SerrePositivity.KST.SConstruction.isInitialVertex_pointCoslice_of_isInvertibleEdge
#print axioms SerrePositivity.KST.SConstruction.isInitialVertex_pointCoslice_of_isInvertibleEdge

#check @SerrePositivity.KST.SConstruction.identityCocone
#print axioms SerrePositivity.KST.SConstruction.identityCocone

#check @SerrePositivity.KST.SConstruction.identityCocone_isColimit
#print axioms SerrePositivity.KST.SConstruction.identityCocone_isColimit

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_of_map_eq
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_of_map_eq

#check @SerrePositivity.KST.SConstruction.identityCocone_val
#print axioms SerrePositivity.KST.SConstruction.identityCocone_val

#check @SerrePositivity.KST.SConstruction.pointCocone_isColimit_of_constant
#print axioms SerrePositivity.KST.SConstruction.pointCocone_isColimit_of_constant

#check @SerrePositivity.KST.SConstruction.horn_one_one_eq_last_face
#print axioms SerrePositivity.KST.SConstruction.horn_one_one_eq_last_face

#check @SerrePositivity.KST.SConstruction.lastVertex_rightAnodyne
#print axioms SerrePositivity.KST.SConstruction.lastVertex_rightAnodyne

#check @SerrePositivity.KST.SConstruction.edgeTargetShape
#print axioms SerrePositivity.KST.SConstruction.edgeTargetShape

#check @SerrePositivity.KST.SConstruction.edgeTargetShape_inl
#print axioms SerrePositivity.KST.SConstruction.edgeTargetShape_inl

#check @SerrePositivity.KST.SConstruction.edgeTargetShape_restrict_last
#print axioms SerrePositivity.KST.SConstruction.edgeTargetShape_restrict_last

#check @SerrePositivity.KST.SConstruction.edgeTargetCocone
#print axioms SerrePositivity.KST.SConstruction.edgeTargetCocone

#check @SerrePositivity.KST.SConstruction.edgeTargetCocone_isColimit
#print axioms SerrePositivity.KST.SConstruction.edgeTargetCocone_isColimit

#check @SerrePositivity.KST.SConstruction.identityLegAttachment_isPushout
#print axioms SerrePositivity.KST.SConstruction.identityLegAttachment_isPushout

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_restrict_of_identity_leg
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_restrict_of_identity_leg

#check @SerrePositivity.KST.SConstruction.spanCoconeSquare_fst_restrict
#print axioms SerrePositivity.KST.SConstruction.spanCoconeSquare_fst_restrict

#check @SerrePositivity.KST.SConstruction.isPushoutSquare_fst
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_fst

#check @SerrePositivity.KST.SConstruction.identityFirstLegAttachment_isPushout
#print axioms SerrePositivity.KST.SConstruction.identityFirstLegAttachment_isPushout

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_restrict_of_identity_first_leg
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_restrict_of_identity_first_leg

#check @SerrePositivity.KST.SConstruction.spanCoconeSquare_snd_restrict
#print axioms SerrePositivity.KST.SConstruction.spanCoconeSquare_snd_restrict

#check @SerrePositivity.KST.SConstruction.isPushoutSquare_snd
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_snd

#check @SerrePositivity.KST.SConstruction.arCofiberSquareOrder_mem_frame
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareOrder_mem_frame

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareOrder
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareOrder

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_inclusion

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt_firstRow
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt_firstRow

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt_diagonal
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt_diagonal

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt_isPushout
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt_isPushout

#check @SerrePositivity.KST.SConstruction.frameCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamily

#check @SerrePositivity.KST.SConstruction.frameCofiberFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamily_vertex

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt_zero_corner
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt_zero_corner

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily_ι
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily_ι

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_apex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_apex

#check @SerrePositivity.KST.SConstruction.frameCofiberFamily_apex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamily_apex

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily_apex
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily_apex

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_vertex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_vertex

#check @SerrePositivity.KST.SConstruction.IsZeroFrameVertex.frameCofiberFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.IsZeroFrameVertex.frameCofiberFamily_vertex

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_ι
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_ι

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_apex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_apex

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_apex
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_apex

#check @SerrePositivity.KST.SConstruction.ihomCurry_pre_whiskerLeft
#print axioms SerrePositivity.KST.SConstruction.ihomCurry_pre_whiskerLeft

#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_frame
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_frame

#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_frame
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_frame

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_bottom
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_bottom

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_input
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_input

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_input
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_input

#check @SerrePositivity.KST.SConstruction.frameInclusion_mono
#print axioms SerrePositivity.KST.SConstruction.frameInclusion_mono

#check @SerrePositivity.KST.SConstruction.exists_arCofiberCompletion_preserving_frame
#print axioms SerrePositivity.KST.SConstruction.exists_arCofiberCompletion_preserving_frame

#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_frame
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_frame

#check @SerrePositivity.KST.SConstruction.exists_firstRowCofiberData_preserving_frame
#print axioms SerrePositivity.KST.SConstruction.exists_firstRowCofiberData_preserving_frame

#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_frame
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_frame

#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_firstRow
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_firstRow

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_hasLiftingProperty_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_hasLiftingProperty_of_vertexSurjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_hasLiftingProperty_boundary
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_hasLiftingProperty_boundary

#check @SerrePositivity.KST.SConstruction.intervalTriple
#print axioms SerrePositivity.KST.SConstruction.intervalTriple

#check @SerrePositivity.KST.SConstruction.arCofiberRectangleOrder
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangleOrder

#check @SerrePositivity.KST.SConstruction.arCofiberRectangle
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangle

#check @SerrePositivity.KST.SConstruction.arCofiberRectangle_left
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangle_left

#check @SerrePositivity.KST.SConstruction.arCofiberRectangle_outer
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangle_outer

#check @SerrePositivity.KST.SConstruction.arCofiberRectangle_right
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangle_right

#check @SerrePositivity.KST.SConstruction.arSquares_isPushout_of_triples
#print axioms SerrePositivity.KST.SConstruction.arSquares_isPushout_of_triples

#check @SerrePositivity.KST.SConstruction.isGapped_iff_triples
#print axioms SerrePositivity.KST.SConstruction.isGapped_iff_triples

#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_zero_diagonal
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_zero_diagonal

#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_firstRow
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_firstRow

#check @SerrePositivity.KST.SConstruction.exists_firstRowDiagramWithZeroDiagonal
#print axioms SerrePositivity.KST.SConstruction.exists_firstRowDiagramWithZeroDiagonal

#check @SerrePositivity.KST.SConstruction.HasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.HasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.exists_pointwiseColimitCone
#print axioms SerrePositivity.KST.SConstruction.exists_pointwiseColimitCone

#check @SerrePositivity.KST.SConstruction.hasColimit_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.hasColimit_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.of_vertexIso
#print axioms SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.of_vertexIso

#check @SerrePositivity.KST.SConstruction.isPointwiseColimitCone_of_isColimitCone_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isPointwiseColimitCone_of_isColimitCone_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_pointwise_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_pointwise_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.isPushoutSquare_iff_pointwise_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_iff_pointwise_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.reindexFunctorCocone
#print axioms SerrePositivity.KST.SConstruction.reindexFunctorCocone

#check @SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.reindex
#print axioms SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.reindex

#check @SerrePositivity.KST.SConstruction.isColimitCone_reindex_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_reindex_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.fullSubcomplex_hasLiftingProperty_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.fullSubcomplex_hasLiftingProperty_of_vertexSurjective

#check @SerrePositivity.KST.SConstruction.isInitialVertex_fullSubcomplex_of_ambient
#print axioms SerrePositivity.KST.SConstruction.isInitialVertex_fullSubcomplex_of_ambient

#check @SerrePositivity.KST.SConstruction.isTerminalVertex_fullSubcomplex_of_ambient
#print axioms SerrePositivity.KST.SConstruction.isTerminalVertex_fullSubcomplex_of_ambient

#check @SerrePositivity.KST.SConstruction.isGapped_const
#print axioms SerrePositivity.KST.SConstruction.isGapped_const

#check @SerrePositivity.KST.SConstruction.sConstructionZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sConstructionZeroVertex

#check @SerrePositivity.KST.SConstruction.sConstructionZeroVertex_isZero
#print axioms SerrePositivity.KST.SConstruction.sConstructionZeroVertex_isZero

#check @SerrePositivity.KST.SConstruction.sMap_zeroVertex
#print axioms SerrePositivity.KST.SConstruction.sMap_zeroVertex

#check @SerrePositivity.KST.SConstruction.sConstruction_hasZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sConstruction_hasZeroVertex

#check @SerrePositivity.KST.SConstruction.sConstructionZero_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sConstructionZero_isZeroVertex

#check @SerrePositivity.KST.SConstruction.sConstructionZero_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.sConstructionZero_isContractibleKan

#check @SerrePositivity.KST.SConstruction.sConstructionZero_kanComplex
#print axioms SerrePositivity.KST.SConstruction.sConstructionZero_kanComplex

#check @SerrePositivity.KST.SConstruction.firstRowZero_hom_ext
#print axioms SerrePositivity.KST.SConstruction.firstRowZero_hom_ext

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_zero_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_zero_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.arSquare_repeat_left
#print axioms SerrePositivity.KST.SConstruction.arSquare_repeat_left

#check @SerrePositivity.KST.SConstruction.arSquare_repeat_right
#print axioms SerrePositivity.KST.SConstruction.arSquare_repeat_right

#check @SerrePositivity.KST.SConstruction.arSquare_isPushout_of_repeated_endpoints
#print axioms SerrePositivity.KST.SConstruction.arSquare_isPushout_of_repeated_endpoints

#check @SerrePositivity.KST.SConstruction.isGapped_one_of_zero_diagonal
#print axioms SerrePositivity.KST.SConstruction.isGapped_one_of_zero_diagonal

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_trivialKanFibration_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_trivialKanFibration_of_vertexSurjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_one_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_one_vertex_surjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_one_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_one_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.arTwoMiddleSquare
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleSquare

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetractionOrder
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetractionOrder

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_order_comp
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_order_comp

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetraction
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetraction

#check @SerrePositivity.KST.SConstruction.arTwoMiddleSquare_retraction
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleSquare_retraction

#check @SerrePositivity.KST.SConstruction.arTwoMiddleSquare_mono
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleSquare_mono

#check @SerrePositivity.KST.SConstruction.arTwoMiddle
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle

#check @SerrePositivity.KST.SConstruction.arTwoMiddleIso
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleIso

#check @SerrePositivity.KST.SConstruction.arTwoMiddleIso_ι
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleIso_ι

#check @SerrePositivity.KST.SConstruction.arTwo_obj_middle_or_endpoint
#print axioms SerrePositivity.KST.SConstruction.arTwo_obj_middle_or_endpoint

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_obj_back
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_obj_back

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_square
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_square

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_mem_of_vertices
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_mem_of_vertices

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_vertices_of_mem
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_vertices_of_mem

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_notMem_first
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_notMem_first

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_notMem_last
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_notMem_last

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_missing_endpoint
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_missing_endpoint

#check @SerrePositivity.KST.SConstruction.exists_arTwo_extension_with_zero_endpoints
#print axioms SerrePositivity.KST.SConstruction.exists_arTwo_extension_with_zero_endpoints

#check @SerrePositivity.KST.SConstruction.isGapped_two_of_cofiber_middle
#print axioms SerrePositivity.KST.SConstruction.isGapped_two_of_cofiber_middle

#check @SerrePositivity.KST.SConstruction.exists_gapped_arTwo_of_cofiber
#print axioms SerrePositivity.KST.SConstruction.exists_gapped_arTwo_of_cofiber

#check @SerrePositivity.KST.SConstruction.firstRow_two_middle_bottom
#print axioms SerrePositivity.KST.SConstruction.firstRow_two_middle_bottom

#check @SerrePositivity.KST.SConstruction.exists_gapped_arTwo_with_firstRow
#print axioms SerrePositivity.KST.SConstruction.exists_gapped_arTwo_with_firstRow

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_two_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_two_vertex_surjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_two_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_two_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.relativeCosliceMap_trivialKanFibration_of_initialBoundaryLifting
#print axioms SerrePositivity.KST.SConstruction.relativeCosliceMap_trivialKanFibration_of_initialBoundaryLifting

#check @SerrePositivity.KST.SConstruction.sliceUnder_empty_hom_ext
#print axioms SerrePositivity.KST.SConstruction.sliceUnder_empty_hom_ext

#check @SerrePositivity.KST.SConstruction.cosliceEndpointMap_trivialKanFibration_of_initialBoundaryLifting
#print axioms SerrePositivity.KST.SConstruction.cosliceEndpointMap_trivialKanFibration_of_initialBoundaryLifting

#check @SerrePositivity.KST.SConstruction.exists_relativeInitialCosliceLift
#print axioms SerrePositivity.KST.SConstruction.exists_relativeInitialCosliceLift

#check @SerrePositivity.KST.SConstruction.stdSimplex_firstVertex_leftAnodyne
#print axioms SerrePositivity.KST.SConstruction.stdSimplex_firstVertex_leftAnodyne

#check @SerrePositivity.KST.SConstruction.pointCosliceVertexOfEdge_projection
#print axioms SerrePositivity.KST.SConstruction.pointCosliceVertexOfEdge_projection

#check @SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_invertibleEdge
#print axioms SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_invertibleEdge

#check @SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_vertexIso
#print axioms SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_vertexIso

#check @SerrePositivity.KST.SConstruction.IsColimitCone.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.IsColimitCone.of_functorIso

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_of_functorIso
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_of_functorIso

#check @SerrePositivity.KST.SConstruction.IsPushoutSquare.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.IsPushoutSquare.of_functorIso

#check @SerrePositivity.KST.SConstruction.exists_initialCoconeVertex_over_invertible_edge
#print axioms SerrePositivity.KST.SConstruction.exists_initialCoconeVertex_over_invertible_edge

#check @SerrePositivity.KST.SConstruction.HasColimit.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.HasColimit.of_functorIso

#check @SerrePositivity.KST.SConstruction.hasColimit_iff_of_functorIso
#print axioms SerrePositivity.KST.SConstruction.hasColimit_iff_of_functorIso

#check @SerrePositivity.KST.SConstruction.zeroSpanData
#print axioms SerrePositivity.KST.SConstruction.zeroSpanData

#check @SerrePositivity.KST.SConstruction.zeroSpanDataProjection
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataProjection

#check @SerrePositivity.KST.SConstruction.zeroSpanDataProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataProjection_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.zeroSpanDataDiagram
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataDiagram

#check @SerrePositivity.KST.SConstruction.zeroSpanDataDiagram_left
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataDiagram_left

#check @SerrePositivity.KST.SConstruction.zeroSpanDataDiagram_right
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataDiagram_right

#check @SerrePositivity.KST.SConstruction.zeroSpan_sources
#print axioms SerrePositivity.KST.SConstruction.zeroSpan_sources

#check @SerrePositivity.KST.SConstruction.zeroSpanDataLift
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataLift

#check @SerrePositivity.KST.SConstruction.zeroSpanDataLift_projection
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataLift_projection

#check @SerrePositivity.KST.SConstruction.zeroSpanDataLift_diagram
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataLift_diagram

#check @SerrePositivity.KST.SConstruction.zeroSpanFamiliesIso
#print axioms SerrePositivity.KST.SConstruction.zeroSpanFamiliesIso

#check @SerrePositivity.KST.SConstruction.zeroSpanDiagramsIso
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDiagramsIso

#check @SerrePositivity.KST.SConstruction.hasColimit_zeroSpan
#print axioms SerrePositivity.KST.SConstruction.hasColimit_zeroSpan

#check @SerrePositivity.KST.SConstruction.cofiberSpan
#print axioms SerrePositivity.KST.SConstruction.cofiberSpan

#check @SerrePositivity.KST.SConstruction.isZeroTargetArrow_pushoutSpan_iff
#print axioms SerrePositivity.KST.SConstruction.isZeroTargetArrow_pushoutSpan_iff

#check @SerrePositivity.KST.SConstruction.zeroSpanFamily_hasColimits
#print axioms SerrePositivity.KST.SConstruction.zeroSpanFamily_hasColimits

#check @SerrePositivity.KST.SConstruction.exists_relative_cofiberFamily_over_span
#print axioms SerrePositivity.KST.SConstruction.exists_relative_cofiberFamily_over_span

#check @SerrePositivity.KST.SConstruction.cofiberSpan_pullback_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.cofiberSpan_pullback_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.cofiberSpan_vertexFiber_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.cofiberSpan_vertexFiber_isContractibleKan

#check @SerrePositivity.KST.SConstruction.IsZeroSpanVertex
#print axioms SerrePositivity.KST.SConstruction.IsZeroSpanVertex

#check @SerrePositivity.KST.SConstruction.zeroSpanDiagrams
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDiagrams

#check @SerrePositivity.KST.SConstruction.zeroSpanDiagrams_quasicategory
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDiagrams_quasicategory

#check @SerrePositivity.KST.SConstruction.cofiberSpanProjection
#print axioms SerrePositivity.KST.SConstruction.cofiberSpanProjection

#check @SerrePositivity.KST.SConstruction.cofiberSpanProjection_ι
#print axioms SerrePositivity.KST.SConstruction.cofiberSpanProjection_ι

#check @SerrePositivity.KST.SConstruction.cofiberSpanProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.cofiberSpanProjection_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.arCofiberZeroInputOrder
#print axioms SerrePositivity.KST.SConstruction.arCofiberZeroInputOrder

#check @SerrePositivity.KST.SConstruction.arCofiberZeroInputMap
#print axioms SerrePositivity.KST.SConstruction.arCofiberZeroInputMap

#check @SerrePositivity.KST.SConstruction.arCofiberInputs_commonSource
#print axioms SerrePositivity.KST.SConstruction.arCofiberInputs_commonSource

#check @SerrePositivity.KST.SConstruction.arCofiberSpan_isPushout
#print axioms SerrePositivity.KST.SConstruction.arCofiberSpan_isPushout

#check @SerrePositivity.KST.SConstruction.arCofiberSpanMap
#print axioms SerrePositivity.KST.SConstruction.arCofiberSpanMap

#check @SerrePositivity.KST.SConstruction.arCofiberSpanMap_left
#print axioms SerrePositivity.KST.SConstruction.arCofiberSpanMap_left

#check @SerrePositivity.KST.SConstruction.arCofiberSpanMap_right
#print axioms SerrePositivity.KST.SConstruction.arCofiberSpanMap_right

#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_left
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_left

#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_span
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_span

#check @SerrePositivity.KST.SConstruction.frameCofiberSpanOperator
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpanOperator

#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_span
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_span

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_span
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_span

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_span
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_span

#check @SerrePositivity.KST.SConstruction.frameCofiberSpanFamily
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpanFamily

#check @SerrePositivity.KST.SConstruction.frameCofiberSpanOperator_vertex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpanOperator_vertex

#check @SerrePositivity.KST.SConstruction.frameCofiberSpanFamily_zero
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpanFamily_zero

#check @SerrePositivity.KST.SConstruction.frameCofiberSpans
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpans

#check @SerrePositivity.KST.SConstruction.frameCofiberSpans_ι
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpans_ι

#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_span
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_span

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_span
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_span

#check @SerrePositivity.KST.SConstruction.exists_arCofiberSpanCompletion_preserving_frame
#print axioms SerrePositivity.KST.SConstruction.exists_arCofiberSpanCompletion_preserving_frame

#check @SerrePositivity.KST.SConstruction.spanTranspose
#print axioms SerrePositivity.KST.SConstruction.spanTranspose

#check @SerrePositivity.KST.SConstruction.spanTranspose_left
#print axioms SerrePositivity.KST.SConstruction.spanTranspose_left

#check @SerrePositivity.KST.SConstruction.spanTranspose_right
#print axioms SerrePositivity.KST.SConstruction.spanTranspose_right

#check @SerrePositivity.KST.SConstruction.spanTranspose_comp_self
#print axioms SerrePositivity.KST.SConstruction.spanTranspose_comp_self

#check @SerrePositivity.KST.SConstruction.spanTransposeIso
#print axioms SerrePositivity.KST.SConstruction.spanTransposeIso

#check @SerrePositivity.KST.SConstruction.spanTranspose_isIso
#print axioms SerrePositivity.KST.SConstruction.spanTranspose_isIso

#check @SerrePositivity.KST.SConstruction.spanTranspose_square
#print axioms SerrePositivity.KST.SConstruction.spanTranspose_square

#check @SerrePositivity.KST.SConstruction.IsPushoutSquare.transpose
#print axioms SerrePositivity.KST.SConstruction.IsPushoutSquare.transpose

#check @SerrePositivity.KST.SConstruction.arVerticalRectangleOrder
#print axioms SerrePositivity.KST.SConstruction.arVerticalRectangleOrder

#check @SerrePositivity.KST.SConstruction.arVerticalRectangle
#print axioms SerrePositivity.KST.SConstruction.arVerticalRectangle

#check @SerrePositivity.KST.SConstruction.arVerticalRectangle_left
#print axioms SerrePositivity.KST.SConstruction.arVerticalRectangle_left

#check @SerrePositivity.KST.SConstruction.arVerticalRectangle_outer
#print axioms SerrePositivity.KST.SConstruction.arVerticalRectangle_outer

#check @SerrePositivity.KST.SConstruction.arVerticalRectangle_right
#print axioms SerrePositivity.KST.SConstruction.arVerticalRectangle_right

#check @SerrePositivity.KST.SConstruction.arTriple_isPushout_of_originSquares
#print axioms SerrePositivity.KST.SConstruction.arTriple_isPushout_of_originSquares

#check @SerrePositivity.KST.SConstruction.isGapped_iff_originSquares
#print axioms SerrePositivity.KST.SConstruction.isGapped_iff_originSquares

#check @SerrePositivity.KST.SConstruction.isGapped_iff_arCofiberFamily_vertices
#print axioms SerrePositivity.KST.SConstruction.isGapped_iff_arCofiberFamily_vertices

#check @SerrePositivity.KST.SConstruction.intervalMaxOrder
#print axioms SerrePositivity.KST.SConstruction.intervalMaxOrder

#check @SerrePositivity.KST.SConstruction.intervalMax
#print axioms SerrePositivity.KST.SConstruction.intervalMax

#check @SerrePositivity.KST.SConstruction.intervalMax_zero
#print axioms SerrePositivity.KST.SConstruction.intervalMax_zero

#check @SerrePositivity.KST.SConstruction.intervalMax_one
#print axioms SerrePositivity.KST.SConstruction.intervalMax_one

#check @SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism
#print axioms SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism

#check @SerrePositivity.KST.SConstruction.cofiberUnitCorner
#print axioms SerrePositivity.KST.SConstruction.cofiberUnitCorner

#check @SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism_zero
#print axioms SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism_zero

#check @SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism_one
#print axioms SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism_one

#check @SerrePositivity.KST.SConstruction.arCofiberUnitSquare
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitSquare

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism_zero
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism_zero

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism_one
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism_one

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism_lower
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism_lower

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism_upper
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism_upper

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_row_right
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_row_right

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism_vertex_constant
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism_vertex_constant

#check @SerrePositivity.KST.SConstruction.arCofiberUnitComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitComparisonIso

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_evaluate
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_evaluate

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_frame
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_frame

#check @SerrePositivity.KST.SConstruction.arSquareFamilyUnitComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyUnitComparisonIso

#check @SerrePositivity.KST.SConstruction.cofiberFamilyUnitComparisonIso
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyUnitComparisonIso

#check @SerrePositivity.KST.SConstruction.squareHorizontalPrism
#print axioms SerrePositivity.KST.SConstruction.squareHorizontalPrism

#check @SerrePositivity.KST.SConstruction.squareVerticalPrism
#print axioms SerrePositivity.KST.SConstruction.squareVerticalPrism

#check @SerrePositivity.KST.SConstruction.cofiberTopCorner
#print axioms SerrePositivity.KST.SConstruction.cofiberTopCorner

#check @SerrePositivity.KST.SConstruction.squareHorizontalPrism_zero
#print axioms SerrePositivity.KST.SConstruction.squareHorizontalPrism_zero

#check @SerrePositivity.KST.SConstruction.squareHorizontalPrism_one
#print axioms SerrePositivity.KST.SConstruction.squareHorizontalPrism_one

#check @SerrePositivity.KST.SConstruction.squareVerticalPrism_zero
#print axioms SerrePositivity.KST.SConstruction.squareVerticalPrism_zero

#check @SerrePositivity.KST.SConstruction.squareVerticalPrism_one
#print axioms SerrePositivity.KST.SConstruction.squareVerticalPrism_one

#check @SerrePositivity.KST.SConstruction.arFixedStartSquare
#print axioms SerrePositivity.KST.SConstruction.arFixedStartSquare

#check @SerrePositivity.KST.SConstruction.arCofiberComparisonSquare
#print axioms SerrePositivity.KST.SConstruction.arCofiberComparisonSquare

#check @SerrePositivity.KST.SConstruction.arCofiberComparisonUnitSquare
#print axioms SerrePositivity.KST.SConstruction.arCofiberComparisonUnitSquare

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism

#check @SerrePositivity.KST.SConstruction.arFixedStartSquare_unitCorner
#print axioms SerrePositivity.KST.SConstruction.arFixedStartSquare_unitCorner

#check @SerrePositivity.KST.SConstruction.arSquare_topCorner
#print axioms SerrePositivity.KST.SConstruction.arSquare_topCorner

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_zero
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_zero

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_one
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_one

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism_zero
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism_zero

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism_one
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism_one

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism_zero
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism_zero

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism_one
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism_one

#check @SerrePositivity.KST.SConstruction.squareVertexLine
#print axioms SerrePositivity.KST.SConstruction.squareVertexLine

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_left
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_left

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_right
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_right

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism_left
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism_left

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism_right
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism_right

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism_lower
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism_lower

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism_upper
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism_upper

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_diagonal_horizontal
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_diagonal_horizontal

#check @SerrePositivity.KST.SConstruction.arCofiberZeroInputMap_fixedStart
#print axioms SerrePositivity.KST.SConstruction.arCofiberZeroInputMap_fixedStart

#check @SerrePositivity.KST.SConstruction.arCofiberInputMap_fixedTarget
#print axioms SerrePositivity.KST.SConstruction.arCofiberInputMap_fixedTarget

#check @SerrePositivity.KST.SConstruction.functorIsoOfSquareConstantPrism
#print axioms SerrePositivity.KST.SConstruction.functorIsoOfSquareConstantPrism

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_constant
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_constant

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism_constant
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism_constant

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism_constant
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism_constant

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalComparisonIso

#check @SerrePositivity.KST.SConstruction.arCofiberTargetComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetComparisonIso

#check @SerrePositivity.KST.SConstruction.arCofiberSourceComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourceComparisonIso

#check @SerrePositivity.KST.SConstruction.arCofiberSelectedSquareComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberSelectedSquareComparisonIso

#check @SerrePositivity.KST.SConstruction.arCofiberCanonicalSquareComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberCanonicalSquareComparisonIso

#check @SerrePositivity.KST.SConstruction.arSquareFamilyApex
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyApex

#check @SerrePositivity.KST.SConstruction.arSquareFamilyApex_frame
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyApex_frame

#check @SerrePositivity.KST.SConstruction.isGapped_arSquareFamilyApex
#print axioms SerrePositivity.KST.SConstruction.isGapped_arSquareFamilyApex

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_span
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_span

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_left
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_left

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_bottom
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_bottom

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_at
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_at

#check @SerrePositivity.KST.SConstruction.isGapped_cofiberFamily_of_fixed_span
#print axioms SerrePositivity.KST.SConstruction.isGapped_cofiberFamily_of_fixed_span

#check @SerrePositivity.KST.SConstruction.frameCofiberFamily_span
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamily_span

#check @SerrePositivity.KST.SConstruction.exists_cofiberFamily_of_zeroFrame
#print axioms SerrePositivity.KST.SConstruction.exists_cofiberFamily_of_zeroFrame

#check @SerrePositivity.KST.SConstruction.exists_gapped_extension_of_zeroFrame
#print axioms SerrePositivity.KST.SConstruction.exists_gapped_extension_of_zeroFrame

#check @SerrePositivity.KST.SConstruction.zeroFrameVertex_of_zero_diagonal
#print axioms SerrePositivity.KST.SConstruction.zeroFrameVertex_of_zero_diagonal

#check @SerrePositivity.KST.SConstruction.exists_gapped_with_firstRow
#print axioms SerrePositivity.KST.SConstruction.exists_gapped_with_firstRow

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_vertex_surjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_vertexFiber_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_vertexFiber_isContractibleKan

#check @SerrePositivity.KST.SConstruction.firstRowEquivalence
#print axioms SerrePositivity.KST.SConstruction.firstRowEquivalence

#check @SerrePositivity.KST.SConstruction.coreSConstruction
#print axioms SerrePositivity.KST.SConstruction.coreSConstruction

#check @SerrePositivity.KST.SConstruction.coreSConstruction_kanComplex
#print axioms SerrePositivity.KST.SConstruction.coreSConstruction_kanComplex

#check @SerrePositivity.KST.SConstruction.coreSMap
#print axioms SerrePositivity.KST.SConstruction.coreSMap

#check @SerrePositivity.KST.SConstruction.simplicialCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.simplicialCoreSConstruction

#check @SerrePositivity.KST.SConstruction.simplicialCoreSConstruction_obj_kanComplex
#print axioms SerrePositivity.KST.SConstruction.simplicialCoreSConstruction_obj_kanComplex

#check @SerrePositivity.KST.SConstruction.coreSConstructionZeroVertex
#print axioms SerrePositivity.KST.SConstruction.coreSConstructionZeroVertex

#check @SerrePositivity.KST.SConstruction.coreSMap_zeroVertex
#print axioms SerrePositivity.KST.SConstruction.coreSMap_zeroVertex

#check @SerrePositivity.KST.SConstruction.diagonalCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.diagonalCoreSConstruction

#check @SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_obj
#print axioms SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_obj

#check @SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_map
#print axioms SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_map

#check @SerrePositivity.KST.SConstruction.kanCoreIso
#print axioms SerrePositivity.KST.SConstruction.kanCoreIso

#check @SerrePositivity.KST.SConstruction.coreSConstructionZero_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.coreSConstructionZero_isContractibleKan

#check @SerrePositivity.KST.SConstruction.pointedCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.pointedCoreSConstruction

#check @SerrePositivity.KST.SConstruction.pointedCoreSConstruction_kanComplex
#print axioms SerrePositivity.KST.SConstruction.pointedCoreSConstruction_kanComplex

#check @SerrePositivity.KST.SConstruction.pointedCoreSMap
#print axioms SerrePositivity.KST.SConstruction.pointedCoreSMap

#check @SerrePositivity.KST.SConstruction.simplicialPointedCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.simplicialPointedCoreSConstruction

#check @SerrePositivity.KST.SConstruction.simplicialPointedCoreSConstruction_forget
#print axioms SerrePositivity.KST.SConstruction.simplicialPointedCoreSConstruction_forget

#check @SerrePositivity.KST.SConstruction.pointedSRealization
#print axioms SerrePositivity.KST.SConstruction.pointedSRealization

#check @SerrePositivity.KST.SConstruction.kanSRealization
#print axioms SerrePositivity.KST.SConstruction.kanSRealization

#check @SerrePositivity.KST.SConstruction.kanSRealization_kanComplex
#print axioms SerrePositivity.KST.SConstruction.kanSRealization_kanComplex

#check @SerrePositivity.KST.SConstruction.sRealizationToKan
#print axioms SerrePositivity.KST.SConstruction.sRealizationToKan

#check @SerrePositivity.KST.SConstruction.sRealizationToKan_anodyne
#print axioms SerrePositivity.KST.SConstruction.sRealizationToKan_anodyne

#check @SerrePositivity.KST.SConstruction.kSpace
#print axioms SerrePositivity.KST.SConstruction.kSpace

#check @SerrePositivity.KST.SConstruction.kSpace_kanComplex
#print axioms SerrePositivity.KST.SConstruction.kSpace_kanComplex

#check @SerrePositivity.KST.SConstruction.diagonalZeroColumn
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroColumn

#check @SerrePositivity.KST.SConstruction.diagonalZeroColumn_zero
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroColumn_zero

#check @SerrePositivity.KST.SConstruction.diagonalZeroColumn_piZero_surjective
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroColumn_piZero_surjective

#check @SerrePositivity.KST.SConstruction.diagonal_preconnected_of_zero
#print axioms SerrePositivity.KST.SConstruction.diagonal_preconnected_of_zero

#check @SerrePositivity.KST.SConstruction.diagonal_connected_of_zero
#print axioms SerrePositivity.KST.SConstruction.diagonal_connected_of_zero

#check @SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_isConnected
#print axioms SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_isConnected

#check @SerrePositivity.KST.SConstruction.mapPiZero_bijective_of_anodyne
#print axioms SerrePositivity.KST.SConstruction.mapPiZero_bijective_of_anodyne

#check @SerrePositivity.KST.SConstruction.isConnected_of_anodyne
#print axioms SerrePositivity.KST.SConstruction.isConnected_of_anodyne

#check @SerrePositivity.KST.SConstruction.sRealizationToKan_piZero_bijective
#print axioms SerrePositivity.KST.SConstruction.sRealizationToKan_piZero_bijective

#check @SerrePositivity.KST.SConstruction.kanSRealization_isConnected
#print axioms SerrePositivity.KST.SConstruction.kanSRealization_isConnected

#check @SerrePositivity.KST.SConstruction.pointedOfVertex_kanComplex
#print axioms SerrePositivity.KST.SConstruction.pointedOfVertex_kanComplex

#check @SerrePositivity.KST.SConstruction.pathEvaluation_eq_evaluateFunctorAt
#print axioms SerrePositivity.KST.SConstruction.pathEvaluation_eq_evaluateFunctorAt

#check @SerrePositivity.KST.SConstruction.pointedPathAt
#print axioms SerrePositivity.KST.SConstruction.pointedPathAt

#check @SerrePositivity.KST.SConstruction.pointedPathEndpoint
#print axioms SerrePositivity.KST.SConstruction.pointedPathEndpoint

#check @SerrePositivity.KST.SConstruction.pointedPathAt_kanComplex
#print axioms SerrePositivity.KST.SConstruction.pointedPathAt_kanComplex

#check @SerrePositivity.KST.SConstruction.pointedPathEndpoint_rlp
#print axioms SerrePositivity.KST.SConstruction.pointedPathEndpoint_rlp

#check @SerrePositivity.KST.SConstruction.loopPathEndpoint
#print axioms SerrePositivity.KST.SConstruction.loopPathEndpoint

#check @SerrePositivity.KST.SConstruction.loopPathEndpoint_rlp
#print axioms SerrePositivity.KST.SConstruction.loopPathEndpoint_rlp

#check @SerrePositivity.KST.SConstruction.loopPathEndpoint_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.loopPathEndpoint_piIsomorphism

#check @SerrePositivity.KST.SConstruction.exists_loopBasepointComparison
#print axioms SerrePositivity.KST.SConstruction.exists_loopBasepointComparison

#check @SerrePositivity.KST.SConstruction.kanComparison_congr_left
#print axioms SerrePositivity.KST.SConstruction.kanComparison_congr_left

#check @SerrePositivity.KST.SConstruction.diagonalZeroVertexEdge
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroVertexEdge

#check @SerrePositivity.KST.SConstruction.realizationZeroPoint
#print axioms SerrePositivity.KST.SConstruction.realizationZeroPoint

#check @SerrePositivity.KST.SConstruction.realizationZeroEdge
#print axioms SerrePositivity.KST.SConstruction.realizationZeroEdge

#check @SerrePositivity.KST.SConstruction.kSpaceAtZero
#print axioms SerrePositivity.KST.SConstruction.kSpaceAtZero

#check @SerrePositivity.KST.SConstruction.kSpaceAtZero_kanComplex
#print axioms SerrePositivity.KST.SConstruction.kSpaceAtZero_kanComplex

#check @SerrePositivity.KST.SConstruction.kSpaceAtZero_comparison
#print axioms SerrePositivity.KST.SConstruction.kSpaceAtZero_comparison

#check @SerrePositivity.KST.SConstruction.ofVertex_basepoint_eq
#print axioms SerrePositivity.KST.SConstruction.ofVertex_basepoint_eq

#check @SerrePositivity.KST.SConstruction.realizationZeroPoint_chosen
#print axioms SerrePositivity.KST.SConstruction.realizationZeroPoint_chosen

#check @SerrePositivity.KST.SConstruction.kSpaceAtZero_chosen
#print axioms SerrePositivity.KST.SConstruction.kSpaceAtZero_chosen

#check @SerrePositivity.KST.SConstruction.kSpace_zeroChoice_comparison
#print axioms SerrePositivity.KST.SConstruction.kSpace_zeroChoice_comparison

#check @SerrePositivity.KST.SConstruction.PreservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.PreservesSConstructionData

#check @SerrePositivity.KST.SConstruction.preservesSConstructionData_id
#print axioms SerrePositivity.KST.SConstruction.preservesSConstructionData_id

#check @SerrePositivity.KST.SConstruction.PreservesSConstructionData.comp
#print axioms SerrePositivity.KST.SConstruction.PreservesSConstructionData.comp

#check @SerrePositivity.KST.SConstruction.IsGapped.postcomp
#print axioms SerrePositivity.KST.SConstruction.IsGapped.postcomp

#check @SerrePositivity.KST.SConstruction.sPostcomp
#print axioms SerrePositivity.KST.SConstruction.sPostcomp

#check @SerrePositivity.KST.SConstruction.sPostcomp_ι
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_ι

#check @SerrePositivity.KST.SConstruction.sPostcomp_id
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_id

#check @SerrePositivity.KST.SConstruction.sPostcomp_comp
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_comp

#check @SerrePositivity.KST.SConstruction.sPostcomp_sMap
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_sMap

#check @SerrePositivity.KST.SConstruction.simplicialSPostcomp
#print axioms SerrePositivity.KST.SConstruction.simplicialSPostcomp

#check @SerrePositivity.KST.SConstruction.simplicialCoreSPostcomp
#print axioms SerrePositivity.KST.SConstruction.simplicialCoreSPostcomp

#check @SerrePositivity.KST.SConstruction.diagonalSPostcomp
#print axioms SerrePositivity.KST.SConstruction.diagonalSPostcomp

#check @SerrePositivity.KST.SConstruction.sPostcomp_zeroVertex
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_zeroVertex

#check @SerrePositivity.KST.SConstruction.diagonalSPostcomp_id
#print axioms SerrePositivity.KST.SConstruction.diagonalSPostcomp_id

#check @SerrePositivity.KST.SConstruction.diagonalSPostcomp_comp
#print axioms SerrePositivity.KST.SConstruction.diagonalSPostcomp_comp

#check @SerrePositivity.KST.SConstruction.diagonalSPostcomp_zeroVertex
#print axioms SerrePositivity.KST.SConstruction.diagonalSPostcomp_zeroVertex

#check @SerrePositivity.KST.SConstruction.PreservesChosenZero
#print axioms SerrePositivity.KST.SConstruction.PreservesChosenZero

#check @SerrePositivity.KST.SConstruction.preservesChosenZero_id
#print axioms SerrePositivity.KST.SConstruction.preservesChosenZero_id

#check @SerrePositivity.KST.SConstruction.PreservesChosenZero.comp
#print axioms SerrePositivity.KST.SConstruction.PreservesChosenZero.comp

#check @SerrePositivity.KST.SConstruction.pointedSPostcomp
#print axioms SerrePositivity.KST.SConstruction.pointedSPostcomp

#check @SerrePositivity.KST.SConstruction.pointedSPostcomp_id
#print axioms SerrePositivity.KST.SConstruction.pointedSPostcomp_id

#check @SerrePositivity.KST.SConstruction.pointedSPostcomp_comp
#print axioms SerrePositivity.KST.SConstruction.pointedSPostcomp_comp

#check @SerrePositivity.KST.SConstruction.kanSPostcomp
#print axioms SerrePositivity.KST.SConstruction.kanSPostcomp

#check @SerrePositivity.KST.SConstruction.kSpacePostcomp
#print axioms SerrePositivity.KST.SConstruction.kSpacePostcomp

#check @SerrePositivity.KST.SConstruction.kSpacePostcomp_id
#print axioms SerrePositivity.KST.SConstruction.kSpacePostcomp_id

#check @SerrePositivity.KST.SConstruction.kSpacePostcomp_comp
#print axioms SerrePositivity.KST.SConstruction.kSpacePostcomp_comp

#check @SerrePositivity.KST.SConstruction.iteratedSConstruction
#print axioms SerrePositivity.KST.SConstruction.iteratedSConstruction

#check @SerrePositivity.KST.SConstruction.iteratedSConstruction_quasicategory
#print axioms SerrePositivity.KST.SConstruction.iteratedSConstruction_quasicategory

#check @SerrePositivity.KST.SConstruction.iteratedSConstruction_hasZeroVertex
#print axioms SerrePositivity.KST.SConstruction.iteratedSConstruction_hasZeroVertex

#check @SerrePositivity.KST.SConstruction.iteratedZeroVertex
#print axioms SerrePositivity.KST.SConstruction.iteratedZeroVertex

#check @SerrePositivity.KST.SConstruction.iteratedCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.iteratedCoreSConstruction

#check @SerrePositivity.KST.SConstruction.iteratedCoreSConstruction_kanComplex
#print axioms SerrePositivity.KST.SConstruction.iteratedCoreSConstruction_kanComplex

#check @SerrePositivity.KST.SConstruction.sConstruction_isZeroVertex_of_contractible
#print axioms SerrePositivity.KST.SConstruction.sConstruction_isZeroVertex_of_contractible

#check @SerrePositivity.KST.SConstruction.sConstruction_isContractibleKan_of_contractible
#print axioms SerrePositivity.KST.SConstruction.sConstruction_isContractibleKan_of_contractible

#check @SerrePositivity.KST.SConstruction.iteratedSConstruction_isContractibleKan_of_zero_mem
#print axioms SerrePositivity.KST.SConstruction.iteratedSConstruction_isContractibleKan_of_zero_mem

#check @SerrePositivity.KST.SConstruction.iteratedCoreSConstruction_isContractibleKan_of_zero_mem
#print axioms SerrePositivity.KST.SConstruction.iteratedCoreSConstruction_isContractibleKan_of_zero_mem

#check @SerrePositivity.KST.SConstruction.mapJoinCocone
#print axioms SerrePositivity.KST.SConstruction.mapJoinCocone

#check @SerrePositivity.KST.SConstruction.sliceUnderPostcomp_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.sliceUnderPostcomp_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_mapJoinCocone_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_mapJoinCocone_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.isZeroVertex_iff_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.isZeroVertex_iff_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.isPushoutSquare_iff_postcomp_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_iff_postcomp_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.isPullbackSquare_iff_postcomp_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.isPullbackSquare_iff_postcomp_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.preservesSConstructionData_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.preservesSConstructionData_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_preservesSConstructionData

#check @SerrePositivity.KST.SConstruction.squareRightEdge_mono
#print axioms SerrePositivity.KST.SConstruction.squareRightEdge_mono

#check @SerrePositivity.KST.SConstruction.squareBottomEdge_mono
#print axioms SerrePositivity.KST.SConstruction.squareBottomEdge_mono

#check @SerrePositivity.KST.SConstruction.hasZeroVertex_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.hasZeroVertex_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.fiberSquare_nonempty_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.fiberSquare_nonempty_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.cofiberSquare_nonempty_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.cofiberSquare_nonempty_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.isStable_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.isStable_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.terminalBoundaryLifting_of_initialBoundaryLifting_op
#print axioms SerrePositivity.KST.SConstruction.terminalBoundaryLifting_of_initialBoundaryLifting_op

#check @SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.op_initial
#print axioms SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.op_initial

#check @SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.of_vertexIso
#print axioms SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.of_vertexIso

#check @SerrePositivity.KST.SConstruction.exists_terminalConeVertex_over_invertible_edge
#print axioms SerrePositivity.KST.SConstruction.exists_terminalConeVertex_over_invertible_edge

#check @SerrePositivity.KST.SConstruction.HasLimit.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.HasLimit.of_functorIso

#check @SerrePositivity.KST.SConstruction.hasLimit_iff_of_functorIso
#print axioms SerrePositivity.KST.SConstruction.hasLimit_iff_of_functorIso

#check @SerrePositivity.KST.SConstruction.zeroCospanData
#print axioms SerrePositivity.KST.SConstruction.zeroCospanData

#check @SerrePositivity.KST.SConstruction.zeroCospanDataProjection
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataProjection

#check @SerrePositivity.KST.SConstruction.zeroCospanDataProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataProjection_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.zeroCospanDataDiagram
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataDiagram

#check @SerrePositivity.KST.SConstruction.zeroCospanDataDiagram_left
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataDiagram_left

#check @SerrePositivity.KST.SConstruction.zeroCospanDataDiagram_right
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataDiagram_right

#check @SerrePositivity.KST.SConstruction.zeroCospan_targets
#print axioms SerrePositivity.KST.SConstruction.zeroCospan_targets

#check @SerrePositivity.KST.SConstruction.zeroCospanDataLift
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataLift

#check @SerrePositivity.KST.SConstruction.zeroCospanDataLift_projection
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataLift_projection

#check @SerrePositivity.KST.SConstruction.zeroCospanDataLift_diagram
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataLift_diagram

#check @SerrePositivity.KST.SConstruction.zeroCospanFamiliesIso
#print axioms SerrePositivity.KST.SConstruction.zeroCospanFamiliesIso

#check @SerrePositivity.KST.SConstruction.zeroCospanDiagramsIso
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDiagramsIso

#check @SerrePositivity.KST.SConstruction.hasLimit_zeroCospan
#print axioms SerrePositivity.KST.SConstruction.hasLimit_zeroCospan

#check @SerrePositivity.KST.SConstruction.fiberSquare_nonempty_of_zeroCospan_limits
#print axioms SerrePositivity.KST.SConstruction.fiberSquare_nonempty_of_zeroCospan_limits

#check @SerrePositivity.KST.SConstruction.functor_const_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.functor_const_isZeroVertex

#check @SerrePositivity.KST.SConstruction.functor_hasZeroVertex
#print axioms SerrePositivity.KST.SConstruction.functor_hasZeroVertex

#check @SerrePositivity.KST.SConstruction.isZeroVertex_evaluateFunctorAt
#print axioms SerrePositivity.KST.SConstruction.isZeroVertex_evaluateFunctorAt

#check @SerrePositivity.KST.SConstruction.cofiberFamilySquare_bottomEdge
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySquare_bottomEdge

#check @SerrePositivity.KST.SConstruction.functor_cofiberSquare_nonempty
#print axioms SerrePositivity.KST.SConstruction.functor_cofiberSquare_nonempty

#check @SerrePositivity.KST.SConstruction.zeroSourceArrow_evaluate
#print axioms SerrePositivity.KST.SConstruction.zeroSourceArrow_evaluate

#check @SerrePositivity.KST.SConstruction.zeroTargetArrow_evaluate
#print axioms SerrePositivity.KST.SConstruction.zeroTargetArrow_evaluate

#check @SerrePositivity.KST.SConstruction.functor_zeroCospan_hasPointwiseLimits
#print axioms SerrePositivity.KST.SConstruction.functor_zeroCospan_hasPointwiseLimits

#check @SerrePositivity.KST.SConstruction.functor_zeroSpan_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.functor_zeroSpan_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.functor_fiberSquare_nonempty
#print axioms SerrePositivity.KST.SConstruction.functor_fiberSquare_nonempty

#check @SerrePositivity.KST.SConstruction.functor_zeroTriangle_pullback_iff
#print axioms SerrePositivity.KST.SConstruction.functor_zeroTriangle_pullback_iff

#check @SerrePositivity.KST.SConstruction.functor_zeroTriangle_pushout_iff
#print axioms SerrePositivity.KST.SConstruction.functor_zeroTriangle_pushout_iff

#check @SerrePositivity.KST.SConstruction.functor_isStable
#print axioms SerrePositivity.KST.SConstruction.functor_isStable

#check @SerrePositivity.KST.SConstruction.sConstruction_isStable
#print axioms SerrePositivity.KST.SConstruction.sConstruction_isStable

#check @SerrePositivity.KST.SConstruction.iteratedSConstruction_isStable
#print axioms SerrePositivity.KST.SConstruction.iteratedSConstruction_isStable

#check @SerrePositivity.KST.SConstruction.map_isZeroVertex_of_zero_image
#print axioms SerrePositivity.KST.SConstruction.map_isZeroVertex_of_zero_image

#check @SerrePositivity.KST.SConstruction.gappedInclusion_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_isZeroVertex

#check @SerrePositivity.KST.SConstruction.sMap_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sMap_isZeroVertex

#check @SerrePositivity.KST.SConstruction.sPostcomp_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_isZeroVertex

#check @SerrePositivity.KST.SConstruction.ihom_postcomp_evaluate
#print axioms SerrePositivity.KST.SConstruction.ihom_postcomp_evaluate

#check @SerrePositivity.KST.SConstruction.functor_reindex_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.functor_reindex_isZeroVertex

#check @SerrePositivity.KST.SConstruction.functor_postcomp_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.functor_postcomp_isZeroVertex

#check @SerrePositivity.KST.SConstruction.functor_reindex_preserves_cofiber
#print axioms SerrePositivity.KST.SConstruction.functor_reindex_preserves_cofiber

#check @SerrePositivity.KST.SConstruction.functor_postcomp_preserves_cofiber
#print axioms SerrePositivity.KST.SConstruction.functor_postcomp_preserves_cofiber

#check @SerrePositivity.KST.SConstruction.InitialBoundaryLifting.comp
#print axioms SerrePositivity.KST.SConstruction.InitialBoundaryLifting.comp

#check @SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.comp
#print axioms SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.comp

#check @SerrePositivity.KST.SConstruction.relativeInitialVertexIso
#print axioms SerrePositivity.KST.SConstruction.relativeInitialVertexIso

#check @SerrePositivity.KST.SConstruction.ihom_pre_innerFibration
#print axioms SerrePositivity.KST.SConstruction.ihom_pre_innerFibration

#check @SerrePositivity.KST.SConstruction.doubleCoconeRestriction
#print axioms SerrePositivity.KST.SConstruction.doubleCoconeRestriction

#check @SerrePositivity.KST.SConstruction.doubleCoconeRestriction_innerFibration
#print axioms SerrePositivity.KST.SConstruction.doubleCoconeRestriction_innerFibration

#check @SerrePositivity.KST.SConstruction.doubleCoconeRestriction_otherOrder
#print axioms SerrePositivity.KST.SConstruction.doubleCoconeRestriction_otherOrder

#check @SerrePositivity.KST.SConstruction.doubleCocone_initial_outer_inner
#print axioms SerrePositivity.KST.SConstruction.doubleCocone_initial_outer_inner

#check @SerrePositivity.KST.SConstruction.doubleCocone_initial_inner_outer
#print axioms SerrePositivity.KST.SConstruction.doubleCocone_initial_inner_outer

#check @SerrePositivity.KST.SConstruction.doubleCoconeUniversalIso
#print axioms SerrePositivity.KST.SConstruction.doubleCoconeUniversalIso

#check @SerrePositivity.KST.SConstruction.colimitInterchange_initialBoundary
#print axioms SerrePositivity.KST.SConstruction.colimitInterchange_initialBoundary

#check @SerrePositivity.KST.SConstruction.colimitCoconeIsoOfDiagramIso
#print axioms SerrePositivity.KST.SConstruction.colimitCoconeIsoOfDiagramIso

#check @SerrePositivity.KST.SConstruction.pushoutSquareIsoOfSpanIso
#print axioms SerrePositivity.KST.SConstruction.pushoutSquareIsoOfSpanIso

#check @SerrePositivity.KST.SConstruction.isZeroVertex_pushout_apex_of_zeroSpan
#print axioms SerrePositivity.KST.SConstruction.isZeroVertex_pushout_apex_of_zeroSpan

#check @SerrePositivity.KST.SConstruction.IsGapped.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.IsGapped.of_functorIso

#check @SerrePositivity.KST.SConstruction.isGapped_iff_of_functorIso
#print axioms SerrePositivity.KST.SConstruction.isGapped_iff_of_functorIso

#check @SerrePositivity.KST.SConstruction.isGapped_of_functorVertex_isZero
#print axioms SerrePositivity.KST.SConstruction.isGapped_of_functorVertex_isZero

#check @SerrePositivity.KST.SConstruction.squareDiagram_pre
#print axioms SerrePositivity.KST.SConstruction.squareDiagram_pre

#check @SerrePositivity.KST.SConstruction.squareDiagram_pushout_iff_initialBoundary
#print axioms SerrePositivity.KST.SConstruction.squareDiagram_pushout_iff_initialBoundary

#check @SerrePositivity.KST.SConstruction.pushoutInterchange
#print axioms SerrePositivity.KST.SConstruction.pushoutInterchange

#check @SerrePositivity.KST.SConstruction.zeroSpanColimit_functorVertex_isZero
#print axioms SerrePositivity.KST.SConstruction.zeroSpanColimit_functorVertex_isZero

#check @SerrePositivity.KST.SConstruction.zeroSpanColimit_all_vertices_zero
#print axioms SerrePositivity.KST.SConstruction.zeroSpanColimit_all_vertices_zero

#check @SerrePositivity.KST.SConstruction.functorVertexEquiv_symm_evaluate
#print axioms SerrePositivity.KST.SConstruction.functorVertexEquiv_symm_evaluate

#check @SerrePositivity.KST.SConstruction.functorVertexEquiv_symm_pre
#print axioms SerrePositivity.KST.SConstruction.functorVertexEquiv_symm_pre

#check @SerrePositivity.KST.SConstruction.gapped_pointwiseColimit_zero_diagonal
#print axioms SerrePositivity.KST.SConstruction.gapped_pointwiseColimit_zero_diagonal

#check @SerrePositivity.KST.SConstruction.gapped_pointwiseColimit
#print axioms SerrePositivity.KST.SConstruction.gapped_pointwiseColimit

#check @SerrePositivity.KST.SConstruction.ihom_fullSubcomplex_hasLiftingProperty_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.ihom_fullSubcomplex_hasLiftingProperty_of_vertexSurjective

#check @SerrePositivity.KST.SConstruction.initialBoundaryLifting_reflect_of_boundary_lifting
#print axioms SerrePositivity.KST.SConstruction.initialBoundaryLifting_reflect_of_boundary_lifting

#check @SerrePositivity.KST.SConstruction.isColimitCone_fullSubcomplex_of_ambient
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_fullSubcomplex_of_ambient

#check @SerrePositivity.KST.SConstruction.exists_gapped_pointwiseColimitCocone
#print axioms SerrePositivity.KST.SConstruction.exists_gapped_pointwiseColimitCocone

#check @SerrePositivity.KST.SConstruction.isColimitCone_gapped_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_gapped_of_pointwise

#check @SerrePositivity.KST.SConstruction.isPointwiseColimitCone_gappedInclusion_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isPointwiseColimitCone_gappedInclusion_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.isColimitCone_gappedInclusion_iff_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_gappedInclusion_iff_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.gappedInclusionZeroTriangle
#print axioms SerrePositivity.KST.SConstruction.gappedInclusionZeroTriangle

#check @SerrePositivity.KST.SConstruction.gappedInclusion_zeroSpan_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_zeroSpan_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.gappedInclusion_cofiber_iff
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_cofiber_iff

#check @SerrePositivity.KST.SConstruction.gappedInclusion_cofiber_iff_pointwise
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_cofiber_iff_pointwise

#check @SerrePositivity.KST.SConstruction.sMap_gapped_evaluate
#print axioms SerrePositivity.KST.SConstruction.sMap_gapped_evaluate

#check @SerrePositivity.KST.SConstruction.sPostcomp_gapped_evaluate
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_gapped_evaluate

#check @SerrePositivity.KST.SConstruction.sMapZeroTriangle
#print axioms SerrePositivity.KST.SConstruction.sMapZeroTriangle

#check @SerrePositivity.KST.SConstruction.sPostcompZeroTriangle
#print axioms SerrePositivity.KST.SConstruction.sPostcompZeroTriangle

#check @SerrePositivity.KST.SConstruction.sMap_preserves_cofiber
#print axioms SerrePositivity.KST.SConstruction.sMap_preserves_cofiber

#check @SerrePositivity.KST.SConstruction.sPostcomp_preserves_cofiber
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_preserves_cofiber

#check @SerrePositivity.KST.SConstruction.PreservesCofiberData
#print axioms SerrePositivity.KST.SConstruction.PreservesCofiberData

#check @SerrePositivity.KST.SConstruction.PreservesSConstructionData.toCofiberData
#print axioms SerrePositivity.KST.SConstruction.PreservesSConstructionData.toCofiberData

#check @SerrePositivity.KST.SConstruction.preservesCofiberData_id
#print axioms SerrePositivity.KST.SConstruction.preservesCofiberData_id

#check @SerrePositivity.KST.SConstruction.PreservesCofiberData.comp
#print axioms SerrePositivity.KST.SConstruction.PreservesCofiberData.comp

#check @SerrePositivity.KST.SConstruction.IsGapped.postcomp_of_cofiber
#print axioms SerrePositivity.KST.SConstruction.IsGapped.postcomp_of_cofiber

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_ι
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_ι

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_eq_sPostcomp
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_eq_sPostcomp

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_gapped_evaluate
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_gapped_evaluate

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_isZeroVertex

#check @SerrePositivity.KST.SConstruction.preservesCofiberData_sPostcompCofiber
#print axioms SerrePositivity.KST.SConstruction.preservesCofiberData_sPostcompCofiber

#check @SerrePositivity.KST.SConstruction.preservesCofiberData_sMap
#print axioms SerrePositivity.KST.SConstruction.preservesCofiberData_sMap

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_id
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_id

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_comp
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_comp

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_sMap
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_sMap

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_zeroVertex
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_zeroVertex

#check @SerrePositivity.KST.SConstruction.StableModel
#print axioms SerrePositivity.KST.SConstruction.StableModel

#check @SerrePositivity.KST.SConstruction.stableModelCategory
#print axioms SerrePositivity.KST.SConstruction.stableModelCategory

#check @SerrePositivity.KST.SConstruction.stableModelForget
#print axioms SerrePositivity.KST.SConstruction.stableModelForget

#check @SerrePositivity.KST.SConstruction.sStableModel
#print axioms SerrePositivity.KST.SConstruction.sStableModel

#check @SerrePositivity.KST.SConstruction.sEndofunctor
#print axioms SerrePositivity.KST.SConstruction.sEndofunctor

#check @SerrePositivity.KST.SConstruction.sEndofunctorMap
#print axioms SerrePositivity.KST.SConstruction.sEndofunctorMap

#check @SerrePositivity.KST.SConstruction.simplicialStableEndofunctor
#print axioms SerrePositivity.KST.SConstruction.simplicialStableEndofunctor

#check @SerrePositivity.KST.SConstruction.multiSEndofunctor
#print axioms SerrePositivity.KST.SConstruction.multiSEndofunctor

#check @SerrePositivity.KST.SConstruction.multiSConstruction
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction

#check @SerrePositivity.KST.SConstruction.multiSConstruction_quasicategory
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_quasicategory

#check @SerrePositivity.KST.SConstruction.multiSConstruction_isStable
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_isStable

#check @SerrePositivity.KST.SConstruction.multiSConstruction_obj_succ
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_obj_succ

#check @SerrePositivity.KST.SConstruction.multiSConstruction_obj_eq_iterated
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_obj_eq_iterated

#check @SerrePositivity.KST.SConstruction.multiCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstruction

#check @SerrePositivity.KST.SConstruction.multiCoreSConstruction_kanComplex
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstruction_kanComplex

#check @SerrePositivity.KST.SConstruction.multiSConstruction_isContractibleKan_of_zero_coordinate
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_isContractibleKan_of_zero_coordinate

#check @SerrePositivity.KST.SConstruction.multiCoreSConstruction_isContractibleKan_of_zero_coordinate
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstruction_isContractibleKan_of_zero_coordinate

#check @SerrePositivity.KST.SConstruction.multiSConstructionFunctor
#print axioms SerrePositivity.KST.SConstruction.multiSConstructionFunctor

#check @SerrePositivity.KST.SConstruction.multiSConstructionFunctor_obj
#print axioms SerrePositivity.KST.SConstruction.multiSConstructionFunctor_obj

#check @SerrePositivity.KST.SConstruction.multiCoreSConstructionFunctor
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstructionFunctor

#check @SerrePositivity.KST.SConstruction.multiCoreSConstructionFunctor_obj
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstructionFunctor_obj

#check @SerrePositivity.KST.SConstruction.multiIndexDiagonal
#print axioms SerrePositivity.KST.SConstruction.multiIndexDiagonal

#check @SerrePositivity.KST.SConstruction.multiDiagonalFunctor
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalFunctor

#check @SerrePositivity.KST.SConstruction.multiRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.multiRealizationFunctor

#check @SerrePositivity.KST.SConstruction.multiDiagonalCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalCoreSConstruction

#check @SerrePositivity.KST.SConstruction.multiDiagonalCoreSConstruction_obj
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalCoreSConstruction_obj

#check @SerrePositivity.KST.SConstruction.StableModel.mk
#print axioms SerrePositivity.KST.SConstruction.StableModel.mk

#check @SerrePositivity.KST.SConstruction.StableModel.carrier
#print axioms SerrePositivity.KST.SConstruction.StableModel.carrier

#check @SerrePositivity.KST.SConstruction.StableModel.quasicategory
#print axioms SerrePositivity.KST.SConstruction.StableModel.quasicategory

#check @SerrePositivity.KST.SConstruction.StableModel.stable
#print axioms SerrePositivity.KST.SConstruction.StableModel.stable

#check @SerrePositivity.KST.SConstruction.simplicialDiagonalFunctor
#print axioms SerrePositivity.KST.SConstruction.simplicialDiagonalFunctor

#check @SerrePositivity.KST.SConstruction.diagonalZeroColumn_mono
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroColumn_mono

#check @SerrePositivity.KST.SConstruction.diagonalZeroColumnNat
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroColumnNat

#check @SerrePositivity.KST.SConstruction.reducedDiagonal
#print axioms SerrePositivity.KST.SConstruction.reducedDiagonal

#check @SerrePositivity.KST.SConstruction.diagonalReductionQuotient
#print axioms SerrePositivity.KST.SConstruction.diagonalReductionQuotient

#check @SerrePositivity.KST.SConstruction.reducedDiagonalMap
#print axioms SerrePositivity.KST.SConstruction.reducedDiagonalMap

#check @SerrePositivity.KST.SConstruction.reducedDiagonalMap_quotient
#print axioms SerrePositivity.KST.SConstruction.reducedDiagonalMap_quotient

#check @SerrePositivity.KST.SConstruction.reducedDiagonalFunctor
#print axioms SerrePositivity.KST.SConstruction.reducedDiagonalFunctor

#check @SerrePositivity.KST.SConstruction.diagonalReductionNat
#print axioms SerrePositivity.KST.SConstruction.diagonalReductionNat

#check @SerrePositivity.KST.SConstruction.map_isIso_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.map_isIso_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.trivialKanFibration_toUnit_of_contractible
#print axioms SerrePositivity.KST.SConstruction.trivialKanFibration_toUnit_of_contractible

#check @SerrePositivity.KST.SConstruction.cofiberQuotient_image_isIso_of_contractible
#print axioms SerrePositivity.KST.SConstruction.cofiberQuotient_image_isIso_of_contractible

#check @SerrePositivity.KST.SConstruction.diagonalReductionQuotient_image_isIso
#print axioms SerrePositivity.KST.SConstruction.diagonalReductionQuotient_image_isIso

#check @SerrePositivity.KST.SConstruction.kanPiIsomorphism_of_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.kanPiIsomorphism_of_localized_isIso

#check @SerrePositivity.KST.SConstruction.pointedKanReplacement_map_piIsomorphism_of_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.pointedKanReplacement_map_piIsomorphism_of_localized_isIso

#check @SerrePositivity.KST.SConstruction.multiDiagonalDiagramFunctor
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalDiagramFunctor

#check @SerrePositivity.KST.SConstruction.multiDiagonalDiagram_zero_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalDiagram_zero_isContractibleKan

#check @SerrePositivity.KST.SConstruction.reducedMultiRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.reducedMultiRealizationFunctor

#check @SerrePositivity.KST.SConstruction.multiRealizationReductionNat
#print axioms SerrePositivity.KST.SConstruction.multiRealizationReductionNat

#check @SerrePositivity.KST.SConstruction.multiRealizationReduction_image_isIso
#print axioms SerrePositivity.KST.SConstruction.multiRealizationReduction_image_isIso

#check @SerrePositivity.KST.SConstruction.reducedMultiKanRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.reducedMultiKanRealizationFunctor

#check @SerrePositivity.KST.SConstruction.reducedMultiKanRealization_kanComplex
#print axioms SerrePositivity.KST.SConstruction.reducedMultiKanRealization_kanComplex

#check @SerrePositivity.KST.SConstruction.reducedKSpaceFunctor
#print axioms SerrePositivity.KST.SConstruction.reducedKSpaceFunctor

#check @SerrePositivity.KST.SConstruction.reducedKSpaceFunctor_kanComplex
#print axioms SerrePositivity.KST.SConstruction.reducedKSpaceFunctor_kanComplex

#check @SerrePositivity.KST.SConstruction.diagonalReductionPointedMap
#print axioms SerrePositivity.KST.SConstruction.diagonalReductionPointedMap

#check @SerrePositivity.KST.SConstruction.diagonalReductionPointedMap_kan_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.diagonalReductionPointedMap_kan_piIsomorphism

#check @SerrePositivity.KST.SConstruction.diagonalReductionLoopMap
#print axioms SerrePositivity.KST.SConstruction.diagonalReductionLoopMap

#check @SerrePositivity.KST.SConstruction.diagonalReductionLoopMap_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.diagonalReductionLoopMap_piIsomorphism

#check @SerrePositivity.KST.SConstruction.multiDiagonalDiagramFunctor_one_obj
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalDiagramFunctor_one_obj

#check @SerrePositivity.KST.SConstruction.reducedSRealizationComparison
#print axioms SerrePositivity.KST.SConstruction.reducedSRealizationComparison

#check @SerrePositivity.KST.SConstruction.reducedSRealizationComparison_kan_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.reducedSRealizationComparison_kan_piIsomorphism

#check @SerrePositivity.KST.SConstruction.kSpaceReductionComparison
#print axioms SerrePositivity.KST.SConstruction.kSpaceReductionComparison

#check @SerrePositivity.KST.SConstruction.kSpaceReductionComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.kSpaceReductionComparison_piIsomorphism

#check @SerrePositivity.KST.SConstruction.reducedSRealizationComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.reducedSRealizationComparison_naturality

#check @SerrePositivity.KST.SConstruction.kSpaceReductionComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.kSpaceReductionComparison_naturality

#check @SerrePositivity.KST.SConstruction.zeroCoordinateFunctor
#print axioms SerrePositivity.KST.SConstruction.zeroCoordinateFunctor

#check @SerrePositivity.KST.SConstruction.zeroCoordinateNat
#print axioms SerrePositivity.KST.SConstruction.zeroCoordinateNat

#check @SerrePositivity.KST.SConstruction.zeroCoordinateRetraction
#print axioms SerrePositivity.KST.SConstruction.zeroCoordinateRetraction

#check @SerrePositivity.KST.SConstruction.zeroCoordinateNat_retraction
#print axioms SerrePositivity.KST.SConstruction.zeroCoordinateNat_retraction

#check @SerrePositivity.KST.SConstruction.zeroDirectionsIndex
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsIndex

#check @SerrePositivity.KST.SConstruction.zeroDirectionsIndexNat
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsIndexNat

#check @SerrePositivity.KST.SConstruction.zeroDirectionsIndexRetraction
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsIndexRetraction

#check @SerrePositivity.KST.SConstruction.zeroDirectionsIndexNat_retraction
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsIndexNat_retraction

#check @SerrePositivity.KST.SConstruction.zeroDirectionsDiagram
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsDiagram

#check @SerrePositivity.KST.SConstruction.zeroDirectionsDiagramMap
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsDiagramMap

#check @SerrePositivity.KST.SConstruction.zeroDirectionsInclusion
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsInclusion

#check @SerrePositivity.KST.SConstruction.zeroDirectionsInclusion_mono
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsInclusion_mono

#check @SerrePositivity.KST.SConstruction.zeroDirectionsDiagram_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsDiagram_isContractibleKan

#check @SerrePositivity.KST.SConstruction.zeroCoordinateEndomorphism
#print axioms SerrePositivity.KST.SConstruction.zeroCoordinateEndomorphism

#check @SerrePositivity.KST.SConstruction.zeroCoordinateEndomorphism_or
#print axioms SerrePositivity.KST.SConstruction.zeroCoordinateEndomorphism_or

#check @SerrePositivity.KST.SConstruction.zeroDirectionsIndexEndomorphism
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsIndexEndomorphism

#check @SerrePositivity.KST.SConstruction.zeroDirectionsIndexEndomorphism_union
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsIndexEndomorphism_union

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRetractionAt
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRetractionAt

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRetractionAt_leftInverse
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRetractionAt_leftInverse

#check @SerrePositivity.KST.SConstruction.zeroDirectionsOperator
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsOperator

#check @SerrePositivity.KST.SConstruction.zeroDirectionsOperator_eq_map
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsOperator_eq_map

#check @SerrePositivity.KST.SConstruction.zeroDirectionsOperator_union
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsOperator_union

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRange
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRange

#check @SerrePositivity.KST.SConstruction.mem_zeroDirectionsRange_iff
#print axioms SerrePositivity.KST.SConstruction.mem_zeroDirectionsRange_iff

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRange_antitone
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRange_antitone

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRange_union
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRange_union

#check @SerrePositivity.KST.SConstruction.zeroDirectionsDiagramToPoint
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsDiagramToPoint

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRealization_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRealization_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRealization_toPoint_image_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRealization_toPoint_image_isIso

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRange_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRange_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.subcomplex_inf_sup
#print axioms SerrePositivity.KST.SConstruction.subcomplex_inf_sup

#check @SerrePositivity.KST.SConstruction.subcomplex_sup_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.subcomplex_sup_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.zeroDirectionsBoundary
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsBoundary

#check @SerrePositivity.KST.SConstruction.zeroDirectionsBoundary_insert
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsBoundary_insert

#check @SerrePositivity.KST.SConstruction.zeroDirectionsBoundary_inf
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsBoundary_inf

#check @SerrePositivity.KST.SConstruction.zeroDirectionsBoundary_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsBoundary_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.zeroDirectionsFatBoundary
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsFatBoundary

#check @SerrePositivity.KST.SConstruction.zeroDirectionsFatBoundary_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsFatBoundary_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRealizationFunctor

#check @SerrePositivity.KST.SConstruction.zeroDirectionsInclusionNat
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsInclusionNat

#check @SerrePositivity.KST.SConstruction.zeroDirectionsInclusionNat_app
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsInclusionNat_app

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRange_image_le
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRange_image_le

#check @SerrePositivity.KST.SConstruction.zeroDirectionsBoundary_image_le
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsBoundary_image_le

#check @SerrePositivity.KST.SConstruction.zeroDirectionsFatBoundaryMap
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsFatBoundaryMap

#check @SerrePositivity.KST.SConstruction.zeroDirectionsFatBoundaryMap_ι
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsFatBoundaryMap_ι

#check @SerrePositivity.KST.SConstruction.boundaryReducedRealization
#print axioms SerrePositivity.KST.SConstruction.boundaryReducedRealization

#check @SerrePositivity.KST.SConstruction.boundaryReductionQuotient
#print axioms SerrePositivity.KST.SConstruction.boundaryReductionQuotient

#check @SerrePositivity.KST.SConstruction.boundaryReducedRealizationMap
#print axioms SerrePositivity.KST.SConstruction.boundaryReducedRealizationMap

#check @SerrePositivity.KST.SConstruction.boundaryReducedRealizationMap_quotient
#print axioms SerrePositivity.KST.SConstruction.boundaryReducedRealizationMap_quotient

#check @SerrePositivity.KST.SConstruction.boundaryReducedRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.boundaryReducedRealizationFunctor

#check @SerrePositivity.KST.SConstruction.boundaryReductionNat
#print axioms SerrePositivity.KST.SConstruction.boundaryReductionNat

#check @SerrePositivity.KST.SConstruction.boundaryReductionQuotient_image_isIso
#print axioms SerrePositivity.KST.SConstruction.boundaryReductionQuotient_image_isIso

#check @SerrePositivity.KST.SConstruction.boundaryKanRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.boundaryKanRealizationFunctor

#check @SerrePositivity.KST.SConstruction.boundaryKanRealization_kanComplex
#print axioms SerrePositivity.KST.SConstruction.boundaryKanRealization_kanComplex

#check @SerrePositivity.KST.SConstruction.cofiberQuotient_image_isIso_of_localized_toPoint
#print axioms SerrePositivity.KST.SConstruction.cofiberQuotient_image_isIso_of_localized_toPoint

#check @SerrePositivity.KST.SConstruction.zeroDirectionsIndexEndomorphism_zero
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsIndexEndomorphism_zero

#check @SerrePositivity.KST.SConstruction.vertex_mem_zeroDirectionsRange
#print axioms SerrePositivity.KST.SConstruction.vertex_mem_zeroDirectionsRange

#check @SerrePositivity.KST.SConstruction.vertex_mem_zeroDirectionsFatBoundary
#print axioms SerrePositivity.KST.SConstruction.vertex_mem_zeroDirectionsFatBoundary

#check @SerrePositivity.KST.SConstruction.cofiberPointedProjection
#print axioms SerrePositivity.KST.SConstruction.cofiberPointedProjection

#check @SerrePositivity.KST.SConstruction.boundaryReductionPointedMap
#print axioms SerrePositivity.KST.SConstruction.boundaryReductionPointedMap

#check @SerrePositivity.KST.SConstruction.boundaryReductionPointedMap_kan_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.boundaryReductionPointedMap_kan_piIsomorphism

#check @SerrePositivity.KST.SConstruction.boundaryReductionLoopMap
#print axioms SerrePositivity.KST.SConstruction.boundaryReductionLoopMap

#check @SerrePositivity.KST.SConstruction.boundaryReductionLoopMap_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.boundaryReductionLoopMap_piIsomorphism

#check @SerrePositivity.KST.SConstruction.boundaryKSpaceFunctor
#print axioms SerrePositivity.KST.SConstruction.boundaryKSpaceFunctor

#check @SerrePositivity.KST.SConstruction.boundaryKSpaceFunctor_kanComplex
#print axioms SerrePositivity.KST.SConstruction.boundaryKSpaceFunctor_kanComplex

#check @SerrePositivity.KST.SConstruction.boundarySRealizationComparison
#print axioms SerrePositivity.KST.SConstruction.boundarySRealizationComparison

#check @SerrePositivity.KST.SConstruction.boundarySRealizationComparison_kan_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.boundarySRealizationComparison_kan_piIsomorphism

#check @SerrePositivity.KST.SConstruction.kSpaceBoundaryComparison
#print axioms SerrePositivity.KST.SConstruction.kSpaceBoundaryComparison

#check @SerrePositivity.KST.SConstruction.kSpaceBoundaryComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.kSpaceBoundaryComparison_piIsomorphism

#check @SerrePositivity.KST.SConstruction.boundarySRealizationComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.boundarySRealizationComparison_naturality

#check @SerrePositivity.KST.SConstruction.kSpaceBoundaryComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.kSpaceBoundaryComparison_naturality

#check @SerrePositivity.KST.SConstruction.diagonalAssembly
#print axioms SerrePositivity.KST.SConstruction.diagonalAssembly

#check @SerrePositivity.KST.SConstruction.diagonalAssembly_naturality
#print axioms SerrePositivity.KST.SConstruction.diagonalAssembly_naturality

#check @SerrePositivity.KST.SConstruction.diagonalAssembly_reindex
#print axioms SerrePositivity.KST.SConstruction.diagonalAssembly_reindex

#check @SerrePositivity.KST.SConstruction.diagonalAssembly_zero
#print axioms SerrePositivity.KST.SConstruction.diagonalAssembly_zero

#check @SerrePositivity.KST.SConstruction.diagonalAssembly_endpoint
#print axioms SerrePositivity.KST.SConstruction.diagonalAssembly_endpoint

#check @SerrePositivity.KST.SConstruction.diagonalAssembly_endpoint_reduced
#print axioms SerrePositivity.KST.SConstruction.diagonalAssembly_endpoint_reduced

#check @SerrePositivity.KST.SConstruction.intervalBoundary_simplex_constant
#print axioms SerrePositivity.KST.SConstruction.intervalBoundary_simplex_constant

#check @SerrePositivity.KST.SConstruction.diagonalAssembly_interval_boundary
#print axioms SerrePositivity.KST.SConstruction.diagonalAssembly_interval_boundary

#check @SerrePositivity.KST.SConstruction.diagonalIntervalComparison
#print axioms SerrePositivity.KST.SConstruction.diagonalIntervalComparison

#check @SerrePositivity.KST.SConstruction.diagonalIntervalComparison_quotient
#print axioms SerrePositivity.KST.SConstruction.diagonalIntervalComparison_quotient

#check @SerrePositivity.KST.SConstruction.diagonalIntervalMap
#print axioms SerrePositivity.KST.SConstruction.diagonalIntervalMap

#check @SerrePositivity.KST.SConstruction.diagonalIntervalMap_quotient
#print axioms SerrePositivity.KST.SConstruction.diagonalIntervalMap_quotient

#check @SerrePositivity.KST.SConstruction.diagonalIntervalFunctor
#print axioms SerrePositivity.KST.SConstruction.diagonalIntervalFunctor

#check @SerrePositivity.KST.SConstruction.diagonalIntervalComparisonNat
#print axioms SerrePositivity.KST.SConstruction.diagonalIntervalComparisonNat

#check @SerrePositivity.KST.SConstruction.coreMap_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.coreMap_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.firstRowOneUnitIso
#print axioms SerrePositivity.KST.SConstruction.firstRowOneUnitIso

#check @SerrePositivity.KST.SConstruction.firstRowOneHomNatIso
#print axioms SerrePositivity.KST.SConstruction.firstRowOneHomNatIso

#check @SerrePositivity.KST.SConstruction.sOneComparison
#print axioms SerrePositivity.KST.SConstruction.sOneComparison

#check @SerrePositivity.KST.SConstruction.sOneComparison_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.sOneComparison_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_sPostcompCofiber
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_sPostcompCofiber

#check @SerrePositivity.KST.SConstruction.sOneComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.sOneComparison_naturality

#check @SerrePositivity.KST.SConstruction.coreSOneComparison
#print axioms SerrePositivity.KST.SConstruction.coreSOneComparison

#check @SerrePositivity.KST.SConstruction.coreSOneComparison_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.coreSOneComparison_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.coreSOneComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.coreSOneComparison_piIsomorphism

#check @SerrePositivity.KST.SConstruction.coreSOneComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.coreSOneComparison_naturality

#check @SerrePositivity.KST.SConstruction.coreSOneComparisonNat
#print axioms SerrePositivity.KST.SConstruction.coreSOneComparisonNat

#check @SerrePositivity.KST.SConstruction.sOneComparison_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.sOneComparison_preservesSConstructionData

#check @SerrePositivity.KST.SConstruction.sOneComparison_preservesCofiberData
#print axioms SerrePositivity.KST.SConstruction.sOneComparison_preservesCofiberData

#check @SerrePositivity.KST.SConstruction.stableSOneComparison
#print axioms SerrePositivity.KST.SConstruction.stableSOneComparison

#check @SerrePositivity.KST.SConstruction.stableSOneComparisonNat
#print axioms SerrePositivity.KST.SConstruction.stableSOneComparisonNat

#check @SerrePositivity.KST.SConstruction.oneDirectionIndex
#print axioms SerrePositivity.KST.SConstruction.oneDirectionIndex

#check @SerrePositivity.KST.SConstruction.multiSOneEndofunctorComparison
#print axioms SerrePositivity.KST.SConstruction.multiSOneEndofunctorComparison

#check @SerrePositivity.KST.SConstruction.multiSOneComparison
#print axioms SerrePositivity.KST.SConstruction.multiSOneComparison

#check @SerrePositivity.KST.SConstruction.multiSOneComparison_app
#print axioms SerrePositivity.KST.SConstruction.multiSOneComparison_app

#check @SerrePositivity.KST.SConstruction.multiSOneComparison_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.multiSOneComparison_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.multiCoreSOneComparison
#print axioms SerrePositivity.KST.SConstruction.multiCoreSOneComparison

#check @SerrePositivity.KST.SConstruction.multiCoreSOneComparison_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.multiCoreSOneComparison_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.oneDirectionDiagonalComparison
#print axioms SerrePositivity.KST.SConstruction.oneDirectionDiagonalComparison

#check @SerrePositivity.KST.SConstruction.oneDirectionRealizationComparison
#print axioms SerrePositivity.KST.SConstruction.oneDirectionRealizationComparison

#check @SerrePositivity.KST.SConstruction.oneDirectionRealizationComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.oneDirectionRealizationComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.multiSOneComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.multiSOneComparison_naturality

#check @SerrePositivity.KST.SConstruction.multiCoreSOneComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.multiCoreSOneComparison_naturality

#check @SerrePositivity.KST.SConstruction.multiCoreSOneComparisonNat
#print axioms SerrePositivity.KST.SConstruction.multiCoreSOneComparisonNat

#check @SerrePositivity.KST.SConstruction.oneDirectionRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.oneDirectionRealizationFunctor

#check @SerrePositivity.KST.SConstruction.oneDirectionRealizationComparisonNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionRealizationComparisonNat

#check @SerrePositivity.KST.SConstruction.oneDirectionRealizationComparisonNat_app
#print axioms SerrePositivity.KST.SConstruction.oneDirectionRealizationComparisonNat_app

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyIndex
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyIndex

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyIndex_naturality
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyIndex_naturality

#check @SerrePositivity.KST.SConstruction.coordinateDiagonalAssembly
#print axioms SerrePositivity.KST.SConstruction.coordinateDiagonalAssembly

#check @SerrePositivity.KST.SConstruction.multiDiagonalAssembly
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalAssembly

#check @SerrePositivity.KST.SConstruction.coordinateDiagonalAssembly_naturality
#print axioms SerrePositivity.KST.SConstruction.coordinateDiagonalAssembly_naturality

#check @SerrePositivity.KST.SConstruction.multiDiagonalAssembly_naturality
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalAssembly_naturality

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyIndex_constant_fixed
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyIndex_constant_fixed

#check @SerrePositivity.KST.SConstruction.multiDiagonalAssembly_constant_mem
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalAssembly_constant_mem

#check @SerrePositivity.KST.SConstruction.multiDiagonalAssembly_boundary_mem
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalAssembly_boundary_mem

#check @SerrePositivity.KST.SConstruction.multiAssemblyBoundaryLift
#print axioms SerrePositivity.KST.SConstruction.multiAssemblyBoundaryLift

#check @SerrePositivity.KST.SConstruction.multiAssemblyBoundaryLift_ι
#print axioms SerrePositivity.KST.SConstruction.multiAssemblyBoundaryLift_ι

#check @SerrePositivity.KST.SConstruction.multiDiagonalAssembly_boundary_condition
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalAssembly_boundary_condition

#check @SerrePositivity.KST.SConstruction.multiIntervalBoundaryComparison
#print axioms SerrePositivity.KST.SConstruction.multiIntervalBoundaryComparison

#check @SerrePositivity.KST.SConstruction.multiIntervalBoundaryComparison_quotient
#print axioms SerrePositivity.KST.SConstruction.multiIntervalBoundaryComparison_quotient

#check @SerrePositivity.KST.SConstruction.intervalBoundaryQuotientFunctor
#print axioms SerrePositivity.KST.SConstruction.intervalBoundaryQuotientFunctor

#check @SerrePositivity.KST.SConstruction.multiIntervalBoundaryFunctor
#print axioms SerrePositivity.KST.SConstruction.multiIntervalBoundaryFunctor

#check @SerrePositivity.KST.SConstruction.multiIntervalBoundaryComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.multiIntervalBoundaryComparison_naturality

#check @SerrePositivity.KST.SConstruction.multiIntervalBoundaryComparisonNat
#print axioms SerrePositivity.KST.SConstruction.multiIntervalBoundaryComparisonNat

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyIndex_zero_commute
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyIndex_zero_commute

#check @SerrePositivity.KST.SConstruction.oneDirectionZeroDiagram
#print axioms SerrePositivity.KST.SConstruction.oneDirectionZeroDiagram

#check @SerrePositivity.KST.SConstruction.oneDirectionZeroInclusion
#print axioms SerrePositivity.KST.SConstruction.oneDirectionZeroInclusion

#check @SerrePositivity.KST.SConstruction.oneDirectionZeroRange
#print axioms SerrePositivity.KST.SConstruction.oneDirectionZeroRange

#check @SerrePositivity.KST.SConstruction.oneDirectionZeroRange_fixed
#print axioms SerrePositivity.KST.SConstruction.oneDirectionZeroRange_fixed

#check @SerrePositivity.KST.SConstruction.multiDiagonalAssembly_zeroRange_mem
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalAssembly_zeroRange_mem

#check @SerrePositivity.KST.SConstruction.oneDirectionFatBoundary
#print axioms SerrePositivity.KST.SConstruction.oneDirectionFatBoundary

#check @SerrePositivity.KST.SConstruction.multiDiagonalAssembly_fatBoundary_mem
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalAssembly_fatBoundary_mem

#check @SerrePositivity.KST.SConstruction.combinedIntervalBoundary
#print axioms SerrePositivity.KST.SConstruction.combinedIntervalBoundary

#check @SerrePositivity.KST.SConstruction.combinedIntervalBoundary_image_le
#print axioms SerrePositivity.KST.SConstruction.combinedIntervalBoundary_image_le

#check @SerrePositivity.KST.SConstruction.combinedAssemblyBoundaryLift
#print axioms SerrePositivity.KST.SConstruction.combinedAssemblyBoundaryLift

#check @SerrePositivity.KST.SConstruction.combinedAssemblyBoundaryLift_ι
#print axioms SerrePositivity.KST.SConstruction.combinedAssemblyBoundaryLift_ι

#check @SerrePositivity.KST.SConstruction.combinedIntervalBoundary_condition
#print axioms SerrePositivity.KST.SConstruction.combinedIntervalBoundary_condition

#check @SerrePositivity.KST.SConstruction.combinedIntervalQuotient
#print axioms SerrePositivity.KST.SConstruction.combinedIntervalQuotient

#check @SerrePositivity.KST.SConstruction.combinedIntervalAssembly
#print axioms SerrePositivity.KST.SConstruction.combinedIntervalAssembly

#check @SerrePositivity.KST.SConstruction.combinedIntervalAssembly_quotient
#print axioms SerrePositivity.KST.SConstruction.combinedIntervalAssembly_quotient

#check @SerrePositivity.KST.SConstruction.oneDirectionZeroRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.oneDirectionZeroRealizationFunctor

#check @SerrePositivity.KST.SConstruction.diagonalZeroInclusion_naturality
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroInclusion_naturality

#check @SerrePositivity.KST.SConstruction.oneDirectionZeroInclusionNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionZeroInclusionNat

#check @SerrePositivity.KST.SConstruction.oneDirectionZeroInclusionNat_app
#print axioms SerrePositivity.KST.SConstruction.oneDirectionZeroInclusionNat_app

#check @SerrePositivity.KST.SConstruction.oneDirectionZeroRange_image_le
#print axioms SerrePositivity.KST.SConstruction.oneDirectionZeroRange_image_le

#check @SerrePositivity.KST.SConstruction.oneDirectionFatBoundary_image_le
#print axioms SerrePositivity.KST.SConstruction.oneDirectionFatBoundary_image_le

#check @SerrePositivity.KST.SConstruction.oneDirectionComparison_zeroRange_image_le
#print axioms SerrePositivity.KST.SConstruction.oneDirectionComparison_zeroRange_image_le

#check @SerrePositivity.KST.SConstruction.oneDirectionComparison_fatBoundary_image_le
#print axioms SerrePositivity.KST.SConstruction.oneDirectionComparison_fatBoundary_image_le

#check @SerrePositivity.KST.SConstruction.oneDirectionBoundaryMap
#print axioms SerrePositivity.KST.SConstruction.oneDirectionBoundaryMap

#check @SerrePositivity.KST.SConstruction.oneDirectionBoundaryMap_ι
#print axioms SerrePositivity.KST.SConstruction.oneDirectionBoundaryMap_ι

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedRealization
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedRealization

#check @SerrePositivity.KST.SConstruction.oneDirectionReductionQuotient
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReductionQuotient

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedRealizationMap
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedRealizationMap

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedRealizationMap_quotient
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedRealizationMap_quotient

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedRealizationFunctor

#check @SerrePositivity.KST.SConstruction.oneDirectionReductionNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReductionNat

#check @SerrePositivity.KST.SConstruction.oneDirectionComparisonBoundaryMap
#print axioms SerrePositivity.KST.SConstruction.oneDirectionComparisonBoundaryMap

#check @SerrePositivity.KST.SConstruction.oneDirectionComparisonBoundaryMap_ι
#print axioms SerrePositivity.KST.SConstruction.oneDirectionComparisonBoundaryMap_ι

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedComparison
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedComparison

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedComparison_quotient
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedComparison_quotient

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedComparison_naturality

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedComparisonNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedComparisonNat

#check @SerrePositivity.KST.SConstruction.coordinateZeroDiagram
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroDiagram

#check @SerrePositivity.KST.SConstruction.coordinateZeroDiagramMap
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroDiagramMap

#check @SerrePositivity.KST.SConstruction.coordinateZeroInclusion
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroInclusion

#check @SerrePositivity.KST.SConstruction.coordinateZeroInclusion_mono
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroInclusion_mono

#check @SerrePositivity.KST.SConstruction.coordinateZeroRetractionAt
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRetractionAt

#check @SerrePositivity.KST.SConstruction.coordinateZeroRetractionAt_leftInverse
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRetractionAt_leftInverse

#check @SerrePositivity.KST.SConstruction.coordinateZeroOperator
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroOperator

#check @SerrePositivity.KST.SConstruction.coordinateZeroOperator_eq_map
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroOperator_eq_map

#check @SerrePositivity.KST.SConstruction.coordinateZeroOperator_union
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroOperator_union

#check @SerrePositivity.KST.SConstruction.coordinateZeroRange
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRange

#check @SerrePositivity.KST.SConstruction.mem_coordinateZeroRange_iff
#print axioms SerrePositivity.KST.SConstruction.mem_coordinateZeroRange_iff

#check @SerrePositivity.KST.SConstruction.coordinateZeroRange_antitone
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRange_antitone

#check @SerrePositivity.KST.SConstruction.coordinateZeroRange_union
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRange_union

#check @SerrePositivity.KST.SConstruction.CoordinateZeroContractible
#print axioms SerrePositivity.KST.SConstruction.CoordinateZeroContractible

#check @SerrePositivity.KST.SConstruction.coordinateZeroDiagramToPoint
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroDiagramToPoint

#check @SerrePositivity.KST.SConstruction.coordinateZeroRealization_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRealization_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.coordinateZeroRange_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRange_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.coordinateZeroBoundary
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroBoundary

#check @SerrePositivity.KST.SConstruction.coordinateZeroBoundary_insert
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroBoundary_insert

#check @SerrePositivity.KST.SConstruction.coordinateZeroBoundary_inf
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroBoundary_inf

#check @SerrePositivity.KST.SConstruction.coordinateZeroBoundary_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroBoundary_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.oneDirection_coordinateZeroContractible
#print axioms SerrePositivity.KST.SConstruction.oneDirection_coordinateZeroContractible

#check @SerrePositivity.KST.SConstruction.oneDirectionFatBoundary_eq_coordinate
#print axioms SerrePositivity.KST.SConstruction.oneDirectionFatBoundary_eq_coordinate

#check @SerrePositivity.KST.SConstruction.oneDirectionFatBoundary_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.oneDirectionFatBoundary_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.oneDirectionReductionQuotient_image_isIso
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReductionQuotient_image_isIso

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedComparison_kan_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedComparison_kan_piIsomorphism

#check @SerrePositivity.KST.SConstruction.oneDirectionKanRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanRealizationFunctor

#check @SerrePositivity.KST.SConstruction.oneDirectionKanRealization_kanComplex
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanRealization_kanComplex

#check @SerrePositivity.KST.SConstruction.oneDirectionKanComparisonNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanComparisonNat

#check @SerrePositivity.KST.SConstruction.oneDirectionLoopComparisonNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionLoopComparisonNat

#check @SerrePositivity.KST.SConstruction.oneDirectionLoopComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.oneDirectionLoopComparison_piIsomorphism

#check @SerrePositivity.KST.SConstruction.tensorCofiberRightSquare
#print axioms SerrePositivity.KST.SConstruction.tensorCofiberRightSquare

#check @SerrePositivity.KST.SConstruction.tensorCofiberLeftSquare
#print axioms SerrePositivity.KST.SConstruction.tensorCofiberLeftSquare

#check @SerrePositivity.KST.SConstruction.tensorCofiberRightDesc
#print axioms SerrePositivity.KST.SConstruction.tensorCofiberRightDesc

#check @SerrePositivity.KST.SConstruction.tensorCofiberRightDesc_quotient
#print axioms SerrePositivity.KST.SConstruction.tensorCofiberRightDesc_quotient

#check @SerrePositivity.KST.SConstruction.tensorCofiberRightDesc_point
#print axioms SerrePositivity.KST.SConstruction.tensorCofiberRightDesc_point

#check @SerrePositivity.KST.SConstruction.tensorCofiberLeftDesc
#print axioms SerrePositivity.KST.SConstruction.tensorCofiberLeftDesc

#check @SerrePositivity.KST.SConstruction.tensorCofiberLeftDesc_quotient
#print axioms SerrePositivity.KST.SConstruction.tensorCofiberLeftDesc_quotient

#check @SerrePositivity.KST.SConstruction.tensorCofiberRightDesc_left_zero
#print axioms SerrePositivity.KST.SConstruction.tensorCofiberRightDesc_left_zero

#check @SerrePositivity.KST.SConstruction.cofiberTensorDesc
#print axioms SerrePositivity.KST.SConstruction.cofiberTensorDesc

#check @SerrePositivity.KST.SConstruction.cofiberTensorDesc_quotient
#print axioms SerrePositivity.KST.SConstruction.cofiberTensorDesc_quotient

#check @SerrePositivity.KST.SConstruction.adjoinTensorMap
#print axioms SerrePositivity.KST.SConstruction.adjoinTensorMap

#check @SerrePositivity.KST.SConstruction.adjoinTensorMap_precomp
#print axioms SerrePositivity.KST.SConstruction.adjoinTensorMap_precomp

#check @SerrePositivity.KST.SConstruction.adjoinTensorMap_zero
#print axioms SerrePositivity.KST.SConstruction.adjoinTensorMap_zero

#check @SerrePositivity.KST.SConstruction.adjoinTensorMap_left_zero
#print axioms SerrePositivity.KST.SConstruction.adjoinTensorMap_left_zero

#check @SerrePositivity.KST.SConstruction.adjoinTensorMap_right_zero
#print axioms SerrePositivity.KST.SConstruction.adjoinTensorMap_right_zero

#check @SerrePositivity.KST.SConstruction.rawCofiberTensorDesc
#print axioms SerrePositivity.KST.SConstruction.rawCofiberTensorDesc

#check @SerrePositivity.KST.SConstruction.rawCofiberTensorDesc_quotient
#print axioms SerrePositivity.KST.SConstruction.rawCofiberTensorDesc_quotient

#check @SerrePositivity.KST.SConstruction.zeroCylinderAssemblyLift
#print axioms SerrePositivity.KST.SConstruction.zeroCylinderAssemblyLift

#check @SerrePositivity.KST.SConstruction.zeroCylinderAssemblyLift_ι
#print axioms SerrePositivity.KST.SConstruction.zeroCylinderAssemblyLift_ι

#check @SerrePositivity.KST.SConstruction.multiDiagonalAssembly_zeroCylinder_condition
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalAssembly_zeroCylinder_condition

#check @SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssembly
#print axioms SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssembly

#check @SerrePositivity.KST.SConstruction.oneDirectionSuspensionProjection
#print axioms SerrePositivity.KST.SConstruction.oneDirectionSuspensionProjection

#check @SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssembly_quotient
#print axioms SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssembly_quotient

#check @SerrePositivity.KST.SConstruction.cofiberProjection_epi
#print axioms SerrePositivity.KST.SConstruction.cofiberProjection_epi

#check @SerrePositivity.KST.SConstruction.cofiberTensorProjection_epi
#print axioms SerrePositivity.KST.SConstruction.cofiberTensorProjection_epi

#check @SerrePositivity.KST.SConstruction.cofiberTensor_hom_ext
#print axioms SerrePositivity.KST.SConstruction.cofiberTensor_hom_ext

#check @SerrePositivity.KST.SConstruction.cofiberProjection_naturality_of_quotient
#print axioms SerrePositivity.KST.SConstruction.cofiberProjection_naturality_of_quotient

#check @SerrePositivity.KST.SConstruction.adjoinTensorMap_postcomp
#print axioms SerrePositivity.KST.SConstruction.adjoinTensorMap_postcomp

#check @SerrePositivity.KST.SConstruction.oneDirectionSuspensionProjection_epi
#print axioms SerrePositivity.KST.SConstruction.oneDirectionSuspensionProjection_epi

#check @SerrePositivity.KST.SConstruction.oneDirectionCofiberProjection_naturality
#print axioms SerrePositivity.KST.SConstruction.oneDirectionCofiberProjection_naturality

#check @SerrePositivity.KST.SConstruction.oneDirectionSuspensionProjection_naturality
#print axioms SerrePositivity.KST.SConstruction.oneDirectionSuspensionProjection_naturality

#check @SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssembly_naturality
#print axioms SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssembly_naturality

#check @SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssemblyNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssemblyNat

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjoint
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjoint

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjoint_naturality
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjoint_naturality

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjointNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjointNat

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjoint_uncurry
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjoint_uncurry

#check @SerrePositivity.KST.SConstruction.pointedTransformationArrows
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationArrows

#check @SerrePositivity.KST.SConstruction.pointedTransformationMiddle
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationMiddle

#check @SerrePositivity.KST.SConstruction.pointedTransformationLeft
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationLeft

#check @SerrePositivity.KST.SConstruction.pointedTransformationRight
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationRight

#check @SerrePositivity.KST.SConstruction.pointedTransformation_fac
#print axioms SerrePositivity.KST.SConstruction.pointedTransformation_fac

#check @SerrePositivity.KST.SConstruction.pointedTransformationLeft_mono
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationLeft_mono

#check @SerrePositivity.KST.SConstruction.pointedTransformationRight_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationRight_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.pointedTransformationMiddle_kanComplex
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationMiddle_kanComplex

#check @SerrePositivity.KST.SConstruction.pointedTransformationRight_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationRight_piIsomorphism

#check @SerrePositivity.KST.SConstruction.pointedTransformationLeft_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationLeft_piIsomorphism

#check @SerrePositivity.KST.SConstruction.refinedOneDirectionKanFunctor
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirectionKanFunctor

#check @SerrePositivity.KST.SConstruction.refinedOneDirectionLeftNat
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirectionLeftNat

#check @SerrePositivity.KST.SConstruction.refinedOneDirectionRightNat
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirectionRightNat

#check @SerrePositivity.KST.SConstruction.refinedOneDirection_fac
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirection_fac

#check @SerrePositivity.KST.SConstruction.refinedOneDirectionKan_kanComplex
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirectionKan_kanComplex

#check @SerrePositivity.KST.SConstruction.refinedOneDirectionLeft_mono
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirectionLeft_mono

#check @SerrePositivity.KST.SConstruction.refinedOneDirectionRight_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirectionRight_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.refinedOneDirectionRight_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirectionRight_piIsomorphism

#check @SerrePositivity.KST.SConstruction.refinedOneDirectionLeft_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirectionLeft_piIsomorphism

#check @SerrePositivity.KST.SConstruction.kanTargetSuspensionAssemblyNat
#print axioms SerrePositivity.KST.SConstruction.kanTargetSuspensionAssemblyNat

#check @SerrePositivity.KST.SConstruction.monicSuspensionKanFunctor
#print axioms SerrePositivity.KST.SConstruction.monicSuspensionKanFunctor

#check @SerrePositivity.KST.SConstruction.monicSuspensionAssemblyNat
#print axioms SerrePositivity.KST.SConstruction.monicSuspensionAssemblyNat

#check @SerrePositivity.KST.SConstruction.monicSuspensionComparisonNat
#print axioms SerrePositivity.KST.SConstruction.monicSuspensionComparisonNat

#check @SerrePositivity.KST.SConstruction.monicSuspensionAssembly_fac
#print axioms SerrePositivity.KST.SConstruction.monicSuspensionAssembly_fac

#check @SerrePositivity.KST.SConstruction.monicSuspensionKan_kanComplex
#print axioms SerrePositivity.KST.SConstruction.monicSuspensionKan_kanComplex

#check @SerrePositivity.KST.SConstruction.monicSuspensionAssembly_mono
#print axioms SerrePositivity.KST.SConstruction.monicSuspensionAssembly_mono

#check @SerrePositivity.KST.SConstruction.monicSuspensionComparison_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.monicSuspensionComparison_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.monicSuspensionComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.monicSuspensionComparison_piIsomorphism

#check @SerrePositivity.KST.SConstruction.pointedExtensionSpace
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionSpace

#check @SerrePositivity.KST.SConstruction.pointedExtensionSpace_projection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionSpace_projection_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.pointedExtensionSpace_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionSpace_isContractibleKan

#check @SerrePositivity.KST.SConstruction.pointedExtensionMap
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionMap

#check @SerrePositivity.KST.SConstruction.pointedExtensionMap_fac
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionMap_fac

#check @SerrePositivity.KST.SConstruction.exists_pointedExtension
#print axioms SerrePositivity.KST.SConstruction.exists_pointedExtension

#check @SerrePositivity.KST.SConstruction.pointedExtensionSpace_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionSpace_relative_lifting

#check @SerrePositivity.KST.SConstruction.loopBoundaryKanFunctor
#print axioms SerrePositivity.KST.SConstruction.loopBoundaryKanFunctor

#check @SerrePositivity.KST.SConstruction.loopBoundaryKan_kanComplex
#print axioms SerrePositivity.KST.SConstruction.loopBoundaryKan_kanComplex

#check @SerrePositivity.KST.SConstruction.kanTargetAssemblyAdjointNat
#print axioms SerrePositivity.KST.SConstruction.kanTargetAssemblyAdjointNat

#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointChoices
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointChoices

#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointChoices_isContractibleKan

#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt

#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_fac
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_fac

#check @SerrePositivity.KST.SConstruction.exists_kanAssemblyAdjoint
#print axioms SerrePositivity.KST.SConstruction.exists_kanAssemblyAdjoint

#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointChoices_kanComplex
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointChoices_kanComplex

#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointChoices_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointChoices_relative_lifting

-- Kan 延長のホモトピー比較と全自然数次数の自然性
#check @SerrePositivity.KST.SConstruction.pointedExtensionVertex
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionVertex
#check @SerrePositivity.KST.SConstruction.pointedExtensionVertex_projection
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionVertex_projection
#check @SerrePositivity.KST.SConstruction.pointedExtensions_nonempty_mappingEdge
#print axioms SerrePositivity.KST.SConstruction.pointedExtensions_nonempty_mappingEdge
#check @SerrePositivity.KST.SConstruction.pointedExtensions_homotopy
#print axioms SerrePositivity.KST.SConstruction.pointedExtensions_homotopy
#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_homotopy
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_homotopy
#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_naturality_homotopy
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_naturality_homotopy
#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_piMap_eq
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_piMap_eq
#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_piMap_naturality
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_piMap_naturality
#check @SerrePositivity.KST.SConstruction.oneDirectionHomotopyFunctor
#print axioms SerrePositivity.KST.SConstruction.oneDirectionHomotopyFunctor
#check @SerrePositivity.KST.SConstruction.loopBoundaryHomotopyFunctor
#print axioms SerrePositivity.KST.SConstruction.loopBoundaryHomotopyFunctor
#check @SerrePositivity.KST.SConstruction.kanAssemblyHomotopyNat
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyHomotopyNat
#check @SerrePositivity.KST.SConstruction.kanAssemblyHomotopyNat_app
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyHomotopyNat_app

-- 同一の反復 S の Kan 列と K 空間を零段とする列
#check @SerrePositivity.KST.SConstruction.oneDirectionKanComparisonInverse
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanComparisonInverse
#check @SerrePositivity.KST.SConstruction.oneDirectionKanComparison_inverse_homotopy
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanComparison_inverse_homotopy
#check @SerrePositivity.KST.SConstruction.oneDirectionKanComparisonInverse_homotopy
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanComparisonInverse_homotopy
#check @SerrePositivity.KST.SConstruction.oneDirectionKanComparisonInverse_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanComparisonInverse_piIsomorphism
#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjoint
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjoint
#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblySigma
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblySigma
#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblySigma_adjoint
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblySigma_adjoint
#check @SerrePositivity.KST.SConstruction.boundaryKanSequence
#print axioms SerrePositivity.KST.SConstruction.boundaryKanSequence
#check @SerrePositivity.KST.SConstruction.monicBoundaryKanSequence
#print axioms SerrePositivity.KST.SConstruction.monicBoundaryKanSequence
#check @SerrePositivity.KST.SConstruction.monicBoundaryKanSequence_sigma_mono
#print axioms SerrePositivity.KST.SConstruction.monicBoundaryKanSequence_sigma_mono
#check @SerrePositivity.KST.SConstruction.monicBoundaryKanSequenceProjection
#print axioms SerrePositivity.KST.SConstruction.monicBoundaryKanSequenceProjection
#check @SerrePositivity.KST.SConstruction.monicBoundaryKanSequenceProjection_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.monicBoundaryKanSequenceProjection_piIsomorphism
#check @SerrePositivity.KST.SConstruction.kKanSequenceLevel
#print axioms SerrePositivity.KST.SConstruction.kKanSequenceLevel
#check @SerrePositivity.KST.SConstruction.kKanSequenceSigma
#print axioms SerrePositivity.KST.SConstruction.kKanSequenceSigma
#check @SerrePositivity.KST.SConstruction.kKanSequence
#print axioms SerrePositivity.KST.SConstruction.kKanSequence
#check @SerrePositivity.KST.SConstruction.kKanSequence_zero_adjoint
#print axioms SerrePositivity.KST.SConstruction.kKanSequence_zero_adjoint
#check @SerrePositivity.KST.SConstruction.kKanSequence_zero_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.kKanSequence_zero_piIsomorphism
#check @SerrePositivity.KST.SConstruction.monicKKanSequence
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequence
#check @SerrePositivity.KST.SConstruction.monicKKanSequence_sigma_mono
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequence_sigma_mono
#check @SerrePositivity.KST.SConstruction.monicKKanSequenceProjection
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequenceProjection
#check @SerrePositivity.KST.SConstruction.monicKKanSequenceProjection_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequenceProjection_piIsomorphism
#check @SerrePositivity.KST.SConstruction.monicKKanSequence_zero
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequence_zero

-- 反復 S の構造射の成分での自然性と単射置換した列間の射
#check @SerrePositivity.KST.SConstruction.pointedComponentInverse_naturality
#print axioms SerrePositivity.KST.SConstruction.pointedComponentInverse_naturality
#check @SerrePositivity.KST.SConstruction.oneDirectionKanComparisonInverse_naturality_component
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanComparisonInverse_naturality_component
#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjoint_naturality_component
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjoint_naturality_component
#check @SerrePositivity.KST.SConstruction.pointedComponentUncurry
#print axioms SerrePositivity.KST.SConstruction.pointedComponentUncurry
#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblySigma_naturality_component
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblySigma_naturality_component
#check @SerrePositivity.KST.SConstruction.pointedLoopCounit_naturality
#print axioms SerrePositivity.KST.SConstruction.pointedLoopCounit_naturality
#check @SerrePositivity.KST.SConstruction.kKanSequenceLevelMap
#print axioms SerrePositivity.KST.SConstruction.kKanSequenceLevelMap
#check @SerrePositivity.KST.SConstruction.kKanSequenceLevelMap_comm
#print axioms SerrePositivity.KST.SConstruction.kKanSequenceLevelMap_comm
#check @SerrePositivity.KST.SConstruction.monicKToRawLevelMap
#print axioms SerrePositivity.KST.SConstruction.monicKToRawLevelMap
#check @SerrePositivity.KST.SConstruction.pointedComponent_sequence_precompose
#print axioms SerrePositivity.KST.SConstruction.pointedComponent_sequence_precompose
#check @SerrePositivity.KST.SConstruction.monicKToRawLevelMap_comm
#print axioms SerrePositivity.KST.SConstruction.monicKToRawLevelMap_comm
#check @SerrePositivity.KST.SConstruction.monicKToRawMap
#print axioms SerrePositivity.KST.SConstruction.monicKToRawMap
#check @SerrePositivity.KST.SConstruction.monicKToRawMap_component
#print axioms SerrePositivity.KST.SConstruction.monicKToRawMap_component
#check @SerrePositivity.KST.SConstruction.monicKKanSequenceProjection_rlp
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequenceProjection_rlp
#check @SerrePositivity.KST.SConstruction.monicKKanSequenceMap
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequenceMap
#check @SerrePositivity.KST.SConstruction.monicKKanSequenceMap_projection
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequenceMap_projection
#check @SerrePositivity.KST.SConstruction.monicKKanSequenceMap_projection_component
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequenceMap_projection_component

-- 候補列の射の成分での関手法則と段ごとの π の自然同型
#check @SerrePositivity.KST.SConstruction.pointedComponent_cancel_right_of_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.pointedComponent_cancel_right_of_piIsomorphism
#check @SerrePositivity.KST.SConstruction.kKanSequenceLevelMap_id
#print axioms SerrePositivity.KST.SConstruction.kKanSequenceLevelMap_id
#check @SerrePositivity.KST.SConstruction.kKanSequenceLevelMap_comp
#print axioms SerrePositivity.KST.SConstruction.kKanSequenceLevelMap_comp
#check @SerrePositivity.KST.SConstruction.monicKKanSequenceMap_id_component
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequenceMap_id_component
#check @SerrePositivity.KST.SConstruction.monicKKanSequenceMap_comp_component
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequenceMap_comp_component
#check @SerrePositivity.KST.SConstruction.pointedHomotopyMap_eq_of_component
#print axioms SerrePositivity.KST.SConstruction.pointedHomotopyMap_eq_of_component
#check @SerrePositivity.KST.SConstruction.kStageHomotopyFunctor
#print axioms SerrePositivity.KST.SConstruction.kStageHomotopyFunctor
#check @SerrePositivity.KST.SConstruction.rawKStageHomotopyFunctor
#print axioms SerrePositivity.KST.SConstruction.rawKStageHomotopyFunctor
#check @SerrePositivity.KST.SConstruction.kStageHomotopyProjection
#print axioms SerrePositivity.KST.SConstruction.kStageHomotopyProjection
#check @SerrePositivity.KST.SConstruction.kStageHomotopyProjection_app_isIso
#print axioms SerrePositivity.KST.SConstruction.kStageHomotopyProjection_app_isIso
#check @SerrePositivity.KST.SConstruction.kStageHomotopyIso
#print axioms SerrePositivity.KST.SConstruction.kStageHomotopyIso

-- 全ての正の反復段の連結性
#check @SerrePositivity.KST.SConstruction.multiDiagonalCoreSConstruction_isConnected
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalCoreSConstruction_isConnected
#check @SerrePositivity.KST.SConstruction.boundaryReductionQuotient_piZero_bijective
#print axioms SerrePositivity.KST.SConstruction.boundaryReductionQuotient_piZero_bijective
#check @SerrePositivity.KST.SConstruction.boundaryReducedRealization_isConnected
#print axioms SerrePositivity.KST.SConstruction.boundaryReducedRealization_isConnected
#check @SerrePositivity.KST.SConstruction.boundaryKanRealization_isConnected
#print axioms SerrePositivity.KST.SConstruction.boundaryKanRealization_isConnected
#check @SerrePositivity.KST.SConstruction.pointedIsConnected_of_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.pointedIsConnected_of_piIsomorphism
#check @SerrePositivity.KST.SConstruction.kKanSequence_positive_isConnected
#print axioms SerrePositivity.KST.SConstruction.kKanSequence_positive_isConnected
#check @SerrePositivity.KST.SConstruction.monicKKanSequence_positive_isConnected
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequence_positive_isConnected

-- 単体的経路構成・実際の収縮・S の経路実現の弱可縮性
#check @SerrePositivity.KST.SConstruction.simplicialPathVertex
#print axioms SerrePositivity.KST.SConstruction.simplicialPathVertex
#check @SerrePositivity.KST.SConstruction.simplicialPathVertex_zero
#print axioms SerrePositivity.KST.SConstruction.simplicialPathVertex_zero
#check @SerrePositivity.KST.SConstruction.simplicialPathVertex_naturality
#print axioms SerrePositivity.KST.SConstruction.simplicialPathVertex_naturality
#check @SerrePositivity.KST.SConstruction.simplicialPath
#print axioms SerrePositivity.KST.SConstruction.simplicialPath
#check @SerrePositivity.KST.SConstruction.simplicialPathAugmentation
#print axioms SerrePositivity.KST.SConstruction.simplicialPathAugmentation
#check @SerrePositivity.KST.SConstruction.augmentedSimplicialPath
#print axioms SerrePositivity.KST.SConstruction.augmentedSimplicialPath
#check @SerrePositivity.KST.SConstruction.simplicialPathExtraDegeneracy
#print axioms SerrePositivity.KST.SConstruction.simplicialPathExtraDegeneracy
#check @SerrePositivity.KST.SConstruction.simplicialPathCut
#print axioms SerrePositivity.KST.SConstruction.simplicialPathCut
#check @SerrePositivity.KST.SConstruction.simplicialPathCut_naturality
#print axioms SerrePositivity.KST.SConstruction.simplicialPathCut_naturality
#check @SerrePositivity.KST.SConstruction.simplicialPathCut_zero
#print axioms SerrePositivity.KST.SConstruction.simplicialPathCut_zero
#check @SerrePositivity.KST.SConstruction.simplicialPathCut_one
#print axioms SerrePositivity.KST.SConstruction.simplicialPathCut_one
#check @SerrePositivity.KST.SConstruction.simplicialPathSection
#print axioms SerrePositivity.KST.SConstruction.simplicialPathSection
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalProjection
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalProjection
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection_projection
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection_projection
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_zero
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_zero
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_one
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_one
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalContraction
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalContraction
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalProjection_image_isIso
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalProjection_image_isIso
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonal_toPoint_image_isIso
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonal_toPoint_image_isIso
#check @SerrePositivity.KST.SConstruction.sPathRealization
#print axioms SerrePositivity.KST.SConstruction.sPathRealization
#check @SerrePositivity.KST.SConstruction.sPathRealizationProjection
#print axioms SerrePositivity.KST.SConstruction.sPathRealizationProjection
#check @SerrePositivity.KST.SConstruction.sPathRealization_toPoint_image_isIso
#print axioms SerrePositivity.KST.SConstruction.sPathRealization_toPoint_image_isIso
#check @SerrePositivity.KST.SConstruction.simplicialPathTail
#print axioms SerrePositivity.KST.SConstruction.simplicialPathTail
#check @SerrePositivity.KST.SConstruction.simplicialPathTail_naturality
#print axioms SerrePositivity.KST.SConstruction.simplicialPathTail_naturality
#check @SerrePositivity.KST.SConstruction.simplicialPathBoundary
#print axioms SerrePositivity.KST.SConstruction.simplicialPathBoundary
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalBoundary
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalBoundary
#check @SerrePositivity.KST.SConstruction.sPathRealizationBoundary
#print axioms SerrePositivity.KST.SConstruction.sPathRealizationBoundary

-- 経路の第一行制限の全単体的自然性・対角比較・S₁ の照合
#check @SerrePositivity.KST.SConstruction.pathFirstRowOrderMap
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowOrderMap
#check @SerrePositivity.KST.SConstruction.pathFirstRowNerveFunctor
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowNerveFunctor
#check @SerrePositivity.KST.SConstruction.pathFirstRowSimplexNatIso
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowSimplexNatIso
#check @SerrePositivity.KST.SConstruction.pathFirstRowInclusion_naturality
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowInclusion_naturality
#check @SerrePositivity.KST.SConstruction.pathFirstRowDiagram
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowDiagram
#check @SerrePositivity.KST.SConstruction.pathFirstRowDiagram_obj_quasicategory
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowDiagram_obj_quasicategory
#check @SerrePositivity.KST.SConstruction.pathFirstRowRestriction
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowRestriction
#check @SerrePositivity.KST.SConstruction.pathFirstRowRestriction_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowRestriction_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.corePathFirstRowRestriction
#print axioms SerrePositivity.KST.SConstruction.corePathFirstRowRestriction
#check @SerrePositivity.KST.SConstruction.corePathFirstRowRestriction_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.corePathFirstRowRestriction_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.pathFirstRowDiagonalComparison
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowDiagonalComparison
#check @SerrePositivity.KST.SConstruction.pathFirstRowDiagonalComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowDiagonalComparison_localized_isIso
#check @SerrePositivity.KST.SConstruction.pathFirstRowDiagramMap
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowDiagramMap
#check @SerrePositivity.KST.SConstruction.pathSConstructionMap
#print axioms SerrePositivity.KST.SConstruction.pathSConstructionMap
#check @SerrePositivity.KST.SConstruction.pathFirstRowRestriction_naturality
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowRestriction_naturality
#check @SerrePositivity.KST.SConstruction.pathFirstRowRestriction_zero
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowRestriction_zero
#check @SerrePositivity.KST.SConstruction.corePathFirstRowRestriction_zero
#print axioms SerrePositivity.KST.SConstruction.corePathFirstRowRestriction_zero

-- S と有限反復 S による trivial Kan fibration の保存
#check @SerrePositivity.KST.SConstruction.ihomMap_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.ihomMap_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.fullSubcomplex_trivialKanFibration_of_reflects
#print axioms SerrePositivity.KST.SConstruction.fullSubcomplex_trivialKanFibration_of_reflects
#check @SerrePositivity.KST.SConstruction.isGapped_iff_postcomp_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.isGapped_iff_postcomp_of_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.multiSEndofunctor_map_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.multiSEndofunctor_map_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.multiCoreSConstructionFunctor_map_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstructionFunctor_map_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.multiRealizationFunctor_map_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.multiRealizationFunctor_map_localized_isIso

-- 経路の第一行比較の安定な入力への束ね・有限反復・弱可縮性
#check @SerrePositivity.KST.SConstruction.stableSPathDiagram
#print axioms SerrePositivity.KST.SConstruction.stableSPathDiagram
#check @SerrePositivity.KST.SConstruction.stablePathFirstRowDiagram
#print axioms SerrePositivity.KST.SConstruction.stablePathFirstRowDiagram
#check @SerrePositivity.KST.SConstruction.stablePathFirstRowRestriction
#print axioms SerrePositivity.KST.SConstruction.stablePathFirstRowRestriction
#check @SerrePositivity.KST.SConstruction.stablePathFirstRowRestriction_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.stablePathFirstRowRestriction_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.stablePathFirstRowRestriction_forget
#print axioms SerrePositivity.KST.SConstruction.stablePathFirstRowRestriction_forget
#check @SerrePositivity.KST.SConstruction.stablePathFirstRowZeroComparison
#print axioms SerrePositivity.KST.SConstruction.stablePathFirstRowZeroComparison
#check @SerrePositivity.KST.SConstruction.stablePathFirstRowRestriction_zero
#print axioms SerrePositivity.KST.SConstruction.stablePathFirstRowRestriction_zero
#check @SerrePositivity.KST.SConstruction.iteratedPathRealizationDiagram
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealizationDiagram
#check @SerrePositivity.KST.SConstruction.iteratedFirstRowRealizationDiagram
#print axioms SerrePositivity.KST.SConstruction.iteratedFirstRowRealizationDiagram
#check @SerrePositivity.KST.SConstruction.iteratedPathFirstRowComparison
#print axioms SerrePositivity.KST.SConstruction.iteratedPathFirstRowComparison
#check @SerrePositivity.KST.SConstruction.iteratedPathFirstRowComparison_app_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.iteratedPathFirstRowComparison_app_localized_isIso
#check @SerrePositivity.KST.SConstruction.iteratedPathRealization
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealization
#check @SerrePositivity.KST.SConstruction.iteratedFirstRowRealization
#print axioms SerrePositivity.KST.SConstruction.iteratedFirstRowRealization
#check @SerrePositivity.KST.SConstruction.iteratedPathFirstRowDiagonalComparison
#print axioms SerrePositivity.KST.SConstruction.iteratedPathFirstRowDiagonalComparison
#check @SerrePositivity.KST.SConstruction.iteratedPathFirstRowDiagonalComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.iteratedPathFirstRowDiagonalComparison_localized_isIso
#check @SerrePositivity.KST.SConstruction.iteratedPathFirstRowComparison_zero
#print axioms SerrePositivity.KST.SConstruction.iteratedPathFirstRowComparison_zero
#check @SerrePositivity.KST.SConstruction.multiSConstruction_isContractibleKan_of_contractible
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_isContractibleKan_of_contractible
#check @SerrePositivity.KST.SConstruction.multiCoreSConstruction_isContractibleKan_of_contractible
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstruction_isContractibleKan_of_contractible
#check @SerrePositivity.KST.SConstruction.multiRealization_toPoint_localized_isIso_of_contractible
#print axioms SerrePositivity.KST.SConstruction.multiRealization_toPoint_localized_isIso_of_contractible
#check @SerrePositivity.KST.SConstruction.iteratedPathRealization_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealization_toPoint_localized_isIso
#check @SerrePositivity.KST.SConstruction.iteratedFirstRowRealization_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.iteratedFirstRowRealization_toPoint_localized_isIso

-- 反復した経路の境界図式と多重実現への全単体的座標同型
#check @SerrePositivity.KST.SConstruction.simplicialPathBoundary_naturality
#print axioms SerrePositivity.KST.SConstruction.simplicialPathBoundary_naturality
#check @SerrePositivity.KST.SConstruction.stableSConstructionDiagram
#print axioms SerrePositivity.KST.SConstruction.stableSConstructionDiagram
#check @SerrePositivity.KST.SConstruction.iteratedSRealizationDiagram
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationDiagram
#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary
#check @SerrePositivity.KST.SConstruction.iteratedSRealization
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealization
#check @SerrePositivity.KST.SConstruction.iteratedPathRealizationBoundary
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealizationBoundary
#check @SerrePositivity.KST.SConstruction.iteratedSRealizationDiagramMap
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationDiagramMap
#check @SerrePositivity.KST.SConstruction.iteratedPathRealizationDiagramMap
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealizationDiagramMap
#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary_naturality
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary_naturality
#check @SerrePositivity.KST.SConstruction.iteratedSRealizationMap
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationMap
#check @SerrePositivity.KST.SConstruction.iteratedPathRealizationMap
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealizationMap
#check @SerrePositivity.KST.SConstruction.iteratedPathRealizationBoundary_naturality
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealizationBoundary_naturality
#check @SerrePositivity.KST.SConstruction.multiSConstruction_diagonal_inner
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_diagonal_inner
#check @SerrePositivity.KST.SConstruction.multiSEndofunctor_diagonal_inner_iso
#print axioms SerrePositivity.KST.SConstruction.multiSEndofunctor_diagonal_inner_iso
#check @SerrePositivity.KST.SConstruction.iteratedSRealization_zero
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealization_zero
#check @SerrePositivity.KST.SConstruction.iteratedPathRealization_zero
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealization_zero
#check @SerrePositivity.KST.SConstruction.iteratedPathRealizationBoundary_zero
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealizationBoundary_zero
#check @SerrePositivity.KST.SConstruction.diagonalSEndofunctor
#print axioms SerrePositivity.KST.SConstruction.diagonalSEndofunctor
#check @SerrePositivity.KST.SConstruction.diagonalSEndofunctor_zero
#print axioms SerrePositivity.KST.SConstruction.diagonalSEndofunctor_zero
#check @SerrePositivity.KST.SConstruction.diagonalSEndofunctor_succ
#print axioms SerrePositivity.KST.SConstruction.diagonalSEndofunctor_succ
#check @SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso
#print axioms SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso
#check @SerrePositivity.KST.SConstruction.stableEndofunctorCoreEvaluation
#print axioms SerrePositivity.KST.SConstruction.stableEndofunctorCoreEvaluation
#check @SerrePositivity.KST.SConstruction.diagonalInnerSCoreDiagram
#print axioms SerrePositivity.KST.SConstruction.diagonalInnerSCoreDiagram
#check @SerrePositivity.KST.SConstruction.diagonalInnerSCoreDiagramIso
#print axioms SerrePositivity.KST.SConstruction.diagonalInnerSCoreDiagramIso
#check @SerrePositivity.KST.SConstruction.diagonalInnerSRealizationIso
#print axioms SerrePositivity.KST.SConstruction.diagonalInnerSRealizationIso
#check @SerrePositivity.KST.SConstruction.iteratedSRealizationInnerIso
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationInnerIso
#check @SerrePositivity.KST.SConstruction.iteratedSRealizationCoordinateIso
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationCoordinateIso
#check @SerrePositivity.KST.SConstruction.canonicalIteratedPathBoundary
#print axioms SerrePositivity.KST.SConstruction.canonicalIteratedPathBoundary
#check @SerrePositivity.KST.SConstruction.reducedIteratedPathBoundary
#print axioms SerrePositivity.KST.SConstruction.reducedIteratedPathBoundary
#check @SerrePositivity.KST.SConstruction.kanIteratedPathBoundary
#print axioms SerrePositivity.KST.SConstruction.kanIteratedPathBoundary

-- 定数経路を潰す点つき反復経路・自然な境界・実際の可縮 Kan 性
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection_mono
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection_mono
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection_naturality
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection_naturality
#check @SerrePositivity.KST.SConstruction.reducedPathDiagonal
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonal
#check @SerrePositivity.KST.SConstruction.pathDiagonalReductionQuotient
#print axioms SerrePositivity.KST.SConstruction.pathDiagonalReductionQuotient
#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalMap
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalMap
#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalMap_quotient
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalMap_quotient
#check @SerrePositivity.KST.SConstruction.pathDiagonalReductionQuotient_image_isIso
#print axioms SerrePositivity.KST.SConstruction.pathDiagonalReductionQuotient_image_isIso
#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalFunctor
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalFunctor
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection_boundary
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection_boundary
#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalBoundary
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalBoundary
#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalBoundary_quotient
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalBoundary_quotient
#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalBoundary_naturality
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalBoundary_naturality
#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalBoundaryNat
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalBoundaryNat
#check @SerrePositivity.KST.SConstruction.pointedIsContractibleKan_of_localized_toPoint
#print axioms SerrePositivity.KST.SConstruction.pointedIsContractibleKan_of_localized_toPoint
#check @SerrePositivity.KST.SConstruction.iteratedSRealizationDiagramFunctor
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationDiagramFunctor
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathFunctor
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathFunctor
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathRealization
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathRealization
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathQuotient
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathQuotient
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathQuotient_image_isIso
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathQuotient_image_isIso
#check @SerrePositivity.KST.SConstruction.pointedIteratedPath_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPath_toPoint_localized_isIso
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathBoundaryNat
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathBoundaryNat
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathBoundary
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathBoundary
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathBoundary_quotient
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathBoundary_quotient
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathKanFunctor
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathKanFunctor
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathKan_kanComplex
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathKan_kanComplex
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathKan_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathKan_toPoint_localized_isIso
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathKan_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathKan_isContractibleKan
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathKanBoundaryNat
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathKanBoundaryNat
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathKanBoundary
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathKanBoundary

-- 最内側の可変次数と最後の零方向の座標比較
#check @SerrePositivity.KST.SConstruction.innerVariableIndex
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex
#check @SerrePositivity.KST.SConstruction.innerVariableSComparisonIso
#print axioms SerrePositivity.KST.SConstruction.innerVariableSComparisonIso
#check @SerrePositivity.KST.SConstruction.innerVariableSMap_succ
#print axioms SerrePositivity.KST.SConstruction.innerVariableSMap_succ
#check @SerrePositivity.KST.SConstruction.innerVariableSComparisonIso_naturality
#print axioms SerrePositivity.KST.SConstruction.innerVariableSComparisonIso_naturality
#check @SerrePositivity.KST.SConstruction.innerVariableIndex_obj_last
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_obj_last
#check @SerrePositivity.KST.SConstruction.innerVariableIndex_obj_castSucc
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_obj_castSucc
#check @SerrePositivity.KST.SConstruction.innerVariableIndex_map_last
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_map_last
#check @SerrePositivity.KST.SConstruction.innerVariableIndex_map_castSucc
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_map_castSucc
#check @SerrePositivity.KST.SConstruction.innerVariableSComparisonNatIso
#print axioms SerrePositivity.KST.SConstruction.innerVariableSComparisonNatIso
#check @SerrePositivity.KST.SConstruction.innerVariableIndex_obj_diagonal
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_obj_diagonal
#check @SerrePositivity.KST.SConstruction.innerVariableIndex_obj_zero
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_obj_zero
#check @SerrePositivity.KST.SConstruction.innerVariableIndex_zero_map
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_zero_map

-- 最内側の零方向の包含の自然変換の比較
#check @SerrePositivity.KST.SConstruction.innerZeroDirectionComparisonIso
#print axioms SerrePositivity.KST.SConstruction.innerZeroDirectionComparisonIso
#check @SerrePositivity.KST.SConstruction.innerDiagonalComparisonIso
#print axioms SerrePositivity.KST.SConstruction.innerDiagonalComparisonIso
#check @SerrePositivity.KST.SConstruction.innerZeroDirectionComparisonIso_inclusion
#print axioms SerrePositivity.KST.SConstruction.innerZeroDirectionComparisonIso_inclusion

-- 内側の零列から全零境界商への自然な点つき比較と経路境界
#check @SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso_zero_app
#print axioms SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso_zero_app
#check @SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso_succ_app
#print axioms SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso_succ_app
#check @SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso_app_eq
#print axioms SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso_app_eq
#check @SerrePositivity.KST.SConstruction.innerDiagonalTransport_succ
#print axioms SerrePositivity.KST.SConstruction.innerDiagonalTransport_succ
#check @SerrePositivity.KST.SConstruction.innerDiagonalComparisonIso_zero_app
#print axioms SerrePositivity.KST.SConstruction.innerDiagonalComparisonIso_zero_app
#check @SerrePositivity.KST.SConstruction.innerDiagonalComparisonIso_succ_app
#print axioms SerrePositivity.KST.SConstruction.innerDiagonalComparisonIso_succ_app
#check @SerrePositivity.KST.SConstruction.innerDiagonalComparisonIso_hom_eq
#print axioms SerrePositivity.KST.SConstruction.innerDiagonalComparisonIso_hom_eq
#check @SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso_app_eq_inner
#print axioms SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso_app_eq_inner
#check @SerrePositivity.KST.SConstruction.iteratedZeroColumnLastZeroPreimage
#print axioms SerrePositivity.KST.SConstruction.iteratedZeroColumnLastZeroPreimage
#check @SerrePositivity.KST.SConstruction.iteratedZeroColumnLastZeroPreimage_fac
#print axioms SerrePositivity.KST.SConstruction.iteratedZeroColumnLastZeroPreimage_fac
#check @SerrePositivity.KST.SConstruction.iteratedZeroColumn_range_le_fatBoundary
#print axioms SerrePositivity.KST.SConstruction.iteratedZeroColumn_range_le_fatBoundary
#check @SerrePositivity.KST.SConstruction.iteratedZeroColumnFatBoundaryLift
#print axioms SerrePositivity.KST.SConstruction.iteratedZeroColumnFatBoundaryLift
#check @SerrePositivity.KST.SConstruction.iteratedZeroColumnFatBoundaryLift_ι
#print axioms SerrePositivity.KST.SConstruction.iteratedZeroColumnFatBoundaryLift_ι
#check @SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparison
#print axioms SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparison
#check @SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparison_quotient
#print axioms SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparison_quotient
#check @SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparison_image_isIso
#print axioms SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparison_image_isIso
#check @SerrePositivity.KST.SConstruction.iteratedSRealizationCoordinateIso_naturality
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationCoordinateIso_naturality
#check @SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparison_naturality
#check @SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparisonNat
#print axioms SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparisonNat
#check @SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparisonKanNat
#print axioms SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparisonKanNat
#check @SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparisonKan_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparisonKan_piIsomorphism
#check @SerrePositivity.KST.SConstruction.pointedFullIteratedPathBoundaryNat
#print axioms SerrePositivity.KST.SConstruction.pointedFullIteratedPathBoundaryNat
#check @SerrePositivity.KST.SConstruction.pointedFullIteratedPathBoundary
#print axioms SerrePositivity.KST.SConstruction.pointedFullIteratedPathBoundary
#check @SerrePositivity.KST.SConstruction.pointedFullIteratedPathBoundary_quotient
#print axioms SerrePositivity.KST.SConstruction.pointedFullIteratedPathBoundary_quotient
#check @SerrePositivity.KST.SConstruction.pointedFullIteratedPathKanBoundaryNat
#print axioms SerrePositivity.KST.SConstruction.pointedFullIteratedPathKanBoundaryNat
#check @SerrePositivity.KST.SConstruction.pointedFullIteratedPathKanBoundary
#print axioms SerrePositivity.KST.SConstruction.pointedFullIteratedPathKanBoundary
#check @SerrePositivity.KST.SConstruction.pointedFullIteratedPathKanBoundary_quotient
#print axioms SerrePositivity.KST.SConstruction.pointedFullIteratedPathKanBoundary_quotient

-- 反復経路境界の path homotopy fiber と loop の自然な比較
#check @SerrePositivity.KST.SConstruction.fiberTerminalInclusion_isIso
#print axioms SerrePositivity.KST.SConstruction.fiberTerminalInclusion_isIso
#check @SerrePositivity.KST.SConstruction.fiberInclusion_piIsomorphism_of_contractible_base
#print axioms SerrePositivity.KST.SConstruction.fiberInclusion_piIsomorphism_of_contractible_base
#check @SerrePositivity.KST.SConstruction.pointedPullbackFiberTo
#print axioms SerrePositivity.KST.SConstruction.pointedPullbackFiberTo
#check @SerrePositivity.KST.SConstruction.pointedPullbackFiberTo_ι
#print axioms SerrePositivity.KST.SConstruction.pointedPullbackFiberTo_ι
#check @SerrePositivity.KST.SConstruction.pointedPullbackFiberFrom
#print axioms SerrePositivity.KST.SConstruction.pointedPullbackFiberFrom
#check @SerrePositivity.KST.SConstruction.pointedPullbackFiberFrom_ι
#print axioms SerrePositivity.KST.SConstruction.pointedPullbackFiberFrom_ι
#check @SerrePositivity.KST.SConstruction.pointedPullbackFiberIso
#print axioms SerrePositivity.KST.SConstruction.pointedPullbackFiberIso
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiber
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiber
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiberProjection
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiberProjection
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiberProjection_fibration
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiberProjection_fibration
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiber_kanComplex
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiber_kanComplex
#check @SerrePositivity.KST.SConstruction.loopPointedPathFiberIso
#print axioms SerrePositivity.KST.SConstruction.loopPointedPathFiberIso
#check @SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber
#print axioms SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber
#check @SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber_projection
#print axioms SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber_projection
#check @SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber_piIsomorphism
#check @SerrePositivity.KST.SConstruction.loopPointedPathFiberIso_hom_ι
#print axioms SerrePositivity.KST.SConstruction.loopPointedPathFiberIso_hom_ι
#check @SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber_path
#print axioms SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber_path
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiberMap
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiberMap
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiberMap_path
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiberMap_path
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiberMap_projection
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiberMap_projection
#check @SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber_naturality
#print axioms SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber_naturality
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiberMap_id
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiberMap_id
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiberMap_comp
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiberMap_comp
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiberFunctorOfNat
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiberFunctorOfNat
#check @SerrePositivity.KST.SConstruction.loopToPathHomotopyFiberNat
#print axioms SerrePositivity.KST.SConstruction.loopToPathHomotopyFiberNat
#check @SerrePositivity.KST.SConstruction.iteratedPathHomotopyFiber
#print axioms SerrePositivity.KST.SConstruction.iteratedPathHomotopyFiber
#check @SerrePositivity.KST.SConstruction.iteratedPathHomotopyFiber_kanComplex
#print axioms SerrePositivity.KST.SConstruction.iteratedPathHomotopyFiber_kanComplex
#check @SerrePositivity.KST.SConstruction.iteratedPathHomotopyFiberMap
#print axioms SerrePositivity.KST.SConstruction.iteratedPathHomotopyFiberMap
#check @SerrePositivity.KST.SConstruction.iteratedPathHomotopyFiberFunctor
#print axioms SerrePositivity.KST.SConstruction.iteratedPathHomotopyFiberFunctor
#check @SerrePositivity.KST.SConstruction.iteratedPathLoopComparison
#print axioms SerrePositivity.KST.SConstruction.iteratedPathLoopComparison
#check @SerrePositivity.KST.SConstruction.iteratedPathLoopComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.iteratedPathLoopComparison_piIsomorphism
#check @SerrePositivity.KST.SConstruction.iteratedPathLoopComparisonNat
#print axioms SerrePositivity.KST.SConstruction.iteratedPathLoopComparisonNat

-- McCarthy 法の全 gapped object 単体集合と加法性の比較射
#check @SerrePositivity.KST.SConstruction.diagonalObjects
#print axioms SerrePositivity.KST.SConstruction.diagonalObjects
#check @SerrePositivity.KST.SConstruction.diagonalObjectInclusion
#print axioms SerrePositivity.KST.SConstruction.diagonalObjectInclusion
#check @SerrePositivity.KST.SConstruction.diagonalObjectInclusionNat
#print axioms SerrePositivity.KST.SConstruction.diagonalObjectInclusionNat
#check @SerrePositivity.KST.SConstruction.objectSConstruction
#print axioms SerrePositivity.KST.SConstruction.objectSConstruction
#check @SerrePositivity.KST.SConstruction.objectSConstruction_obj
#print axioms SerrePositivity.KST.SConstruction.objectSConstruction_obj
#check @SerrePositivity.KST.SConstruction.coreVertexNatIso
#print axioms SerrePositivity.KST.SConstruction.coreVertexNatIso
#check @SerrePositivity.KST.SConstruction.coreDiagramObjectsIso
#print axioms SerrePositivity.KST.SConstruction.coreDiagramObjectsIso
#check @SerrePositivity.KST.SConstruction.objectCoreDiagonalComparisonNat
#print axioms SerrePositivity.KST.SConstruction.objectCoreDiagonalComparisonNat
#check @SerrePositivity.KST.SConstruction.objectSCoreVertexIso
#print axioms SerrePositivity.KST.SConstruction.objectSCoreVertexIso
#check @SerrePositivity.KST.SConstruction.objectToCoreSRealization
#print axioms SerrePositivity.KST.SConstruction.objectToCoreSRealization
#check @SerrePositivity.KST.SConstruction.objectToCoreSRealization_eq
#print axioms SerrePositivity.KST.SConstruction.objectToCoreSRealization_eq
#check @SerrePositivity.KST.SConstruction.objectToCoreSRealization_naturality
#print axioms SerrePositivity.KST.SConstruction.objectToCoreSRealization_naturality
#check @SerrePositivity.KST.SConstruction.objectSConstructionFunctor
#print axioms SerrePositivity.KST.SConstruction.objectSConstructionFunctor
#check @SerrePositivity.KST.SConstruction.objectSConstructionFunctor_obj
#print axioms SerrePositivity.KST.SConstruction.objectSConstructionFunctor_obj
#check @SerrePositivity.KST.SConstruction.sTwoFaceComparisonNat
#print axioms SerrePositivity.KST.SConstruction.sTwoFaceComparisonNat
#check @SerrePositivity.KST.SConstruction.sTwoSubobject
#print axioms SerrePositivity.KST.SConstruction.sTwoSubobject
#check @SerrePositivity.KST.SConstruction.sTwoMiddle
#print axioms SerrePositivity.KST.SConstruction.sTwoMiddle
#check @SerrePositivity.KST.SConstruction.sTwoQuotient
#print axioms SerrePositivity.KST.SConstruction.sTwoQuotient
#check @SerrePositivity.KST.SConstruction.sTwoAdditivityComparisonNat
#print axioms SerrePositivity.KST.SConstruction.sTwoAdditivityComparisonNat
#check @SerrePositivity.KST.SConstruction.sTwoAdditivityComparisonNat_fst
#print axioms SerrePositivity.KST.SConstruction.sTwoAdditivityComparisonNat_fst
#check @SerrePositivity.KST.SConstruction.sTwoAdditivityComparisonNat_snd
#print axioms SerrePositivity.KST.SConstruction.sTwoAdditivityComparisonNat_snd
#check @SerrePositivity.KST.SConstruction.objectSAdditivityComparisonNat
#print axioms SerrePositivity.KST.SConstruction.objectSAdditivityComparisonNat
#check @SerrePositivity.KST.SConstruction.coreSAdditivityComparisonNat
#print axioms SerrePositivity.KST.SConstruction.coreSAdditivityComparisonNat

#check @SerrePositivity.KST.SConstruction.exists_stable_pushoutPresentation_of_span
#print axioms SerrePositivity.KST.SConstruction.exists_stable_pushoutPresentation_of_span
#check @SerrePositivity.KST.SConstruction.exists_stable_pushoutSquare_of_span
#print axioms SerrePositivity.KST.SConstruction.exists_stable_pushoutSquare_of_span
#check @SerrePositivity.KST.SConstruction.stable_hasColimit_span
#print axioms SerrePositivity.KST.SConstruction.stable_hasColimit_span
#check @SerrePositivity.KST.SConstruction.stable_pushoutProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.stable_pushoutProjection_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.exists_relative_stable_pushoutFamily
#print axioms SerrePositivity.KST.SConstruction.exists_relative_stable_pushoutFamily
#check @SerrePositivity.KST.SConstruction.exists_stablePushoutSection_extending
#print axioms SerrePositivity.KST.SConstruction.exists_stablePushoutSection_extending
#check @SerrePositivity.KST.SConstruction.stablePushoutFamilySpace
#print axioms SerrePositivity.KST.SConstruction.stablePushoutFamilySpace
#check @SerrePositivity.KST.SConstruction.stablePushoutFamilySpace_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.stablePushoutFamilySpace_isContractibleKan
#check @SerrePositivity.KST.SConstruction.stablePushoutFamiliesIso
#print axioms SerrePositivity.KST.SConstruction.stablePushoutFamiliesIso
#check @SerrePositivity.KST.SConstruction.stablePushoutSection
#print axioms SerrePositivity.KST.SConstruction.stablePushoutSection
#check @SerrePositivity.KST.SConstruction.stablePushoutSection_projection
#print axioms SerrePositivity.KST.SConstruction.stablePushoutSection_projection
#check @SerrePositivity.KST.SConstruction.stablePushoutFunctor
#print axioms SerrePositivity.KST.SConstruction.stablePushoutFunctor
#check @SerrePositivity.KST.SConstruction.PreservesCofiberData.isPushoutSquare
#print axioms SerrePositivity.KST.SConstruction.PreservesCofiberData.isPushoutSquare
#check @SerrePositivity.KST.SConstruction.PreservesCofiberData.toSConstructionData
#print axioms SerrePositivity.KST.SConstruction.PreservesCofiberData.toSConstructionData
#check @SerrePositivity.KST.SConstruction.preservesSConstructionData_iff_cofiberData
#print axioms SerrePositivity.KST.SConstruction.preservesSConstructionData_iff_cofiberData
#check @SerrePositivity.KST.SConstruction.stableModelHom_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.stableModelHom_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.functor_span_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.functor_span_hasPointwiseColimits
#check @SerrePositivity.KST.SConstruction.functor_pushout_iff_pointwise
#print axioms SerrePositivity.KST.SConstruction.functor_pushout_iff_pointwise
#check @SerrePositivity.KST.SConstruction.gappedInclusion_pushout_iff
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_pushout_iff
#check @SerrePositivity.KST.SConstruction.gappedInclusion_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.gappedInclusion_pushout_iff_pointwise
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_pushout_iff_pointwise
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsPostcomp
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsPostcomp
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsPostcomp_ι
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsPostcomp_ι
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsPostcomp_projection
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsPostcomp_projection
#check @SerrePositivity.KST.SConstruction.stablePushoutSection_postcompIso
#print axioms SerrePositivity.KST.SConstruction.stablePushoutSection_postcompIso

#check @SerrePositivity.KST.SConstruction.identityPushoutShape
#print axioms SerrePositivity.KST.SConstruction.identityPushoutShape
#check @SerrePositivity.KST.SConstruction.identityPushoutShape_isPushout
#print axioms SerrePositivity.KST.SConstruction.identityPushoutShape_isPushout
#check @SerrePositivity.KST.SConstruction.identitySpanShape
#print axioms SerrePositivity.KST.SConstruction.identitySpanShape
#check @SerrePositivity.KST.SConstruction.identitySpanSection
#print axioms SerrePositivity.KST.SConstruction.identitySpanSection
#check @SerrePositivity.KST.SConstruction.identitySpanSection_shape
#print axioms SerrePositivity.KST.SConstruction.identitySpanSection_shape
#check @SerrePositivity.KST.SConstruction.identitySpanFamily
#print axioms SerrePositivity.KST.SConstruction.identitySpanFamily
#check @SerrePositivity.KST.SConstruction.identitySpanFamily_mono
#print axioms SerrePositivity.KST.SConstruction.identitySpanFamily_mono
#check @SerrePositivity.KST.SConstruction.identityPushoutFamily
#print axioms SerrePositivity.KST.SConstruction.identityPushoutFamily
#check @SerrePositivity.KST.SConstruction.identityPushoutFamily_ι
#print axioms SerrePositivity.KST.SConstruction.identityPushoutFamily_ι
#check @SerrePositivity.KST.SConstruction.identityPushoutFamily_projection
#print axioms SerrePositivity.KST.SConstruction.identityPushoutFamily_projection
#check @SerrePositivity.KST.SConstruction.identitySquareReconstruction
#print axioms SerrePositivity.KST.SConstruction.identitySquareReconstruction
#check @SerrePositivity.KST.SConstruction.identitySpanFamily_reconstruction
#print axioms SerrePositivity.KST.SConstruction.identitySpanFamily_reconstruction
#check @SerrePositivity.KST.SConstruction.identitySquareReconstruction_cross
#print axioms SerrePositivity.KST.SConstruction.identitySquareReconstruction_cross
#check @SerrePositivity.KST.SConstruction.identitySquareReconstruction_overlap
#print axioms SerrePositivity.KST.SConstruction.identitySquareReconstruction_overlap
#check @SerrePositivity.KST.SConstruction.subcomplexUnionMap
#print axioms SerrePositivity.KST.SConstruction.subcomplexUnionMap
#check @SerrePositivity.KST.SConstruction.identitySpanSubcomplex
#print axioms SerrePositivity.KST.SConstruction.identitySpanSubcomplex
#check @SerrePositivity.KST.SConstruction.identityUnionSquare
#print axioms SerrePositivity.KST.SConstruction.identityUnionSquare
#check @SerrePositivity.KST.SConstruction.identityUnionSquare_on_family
#print axioms SerrePositivity.KST.SConstruction.identityUnionSquare_on_family
#check @SerrePositivity.KST.SConstruction.identityUnionSquare_span
#print axioms SerrePositivity.KST.SConstruction.identityUnionSquare_span
#check @SerrePositivity.KST.SConstruction.identityUnionPushoutFamily
#print axioms SerrePositivity.KST.SConstruction.identityUnionPushoutFamily
#check @SerrePositivity.KST.SConstruction.identityUnionPushoutFamily_projection
#print axioms SerrePositivity.KST.SConstruction.identityUnionPushoutFamily_projection
#check @SerrePositivity.KST.SConstruction.exists_jointNormalizedPushoutSection
#print axioms SerrePositivity.KST.SConstruction.exists_jointNormalizedPushoutSection
#check @SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection
#print axioms SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection
#check @SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection_projection
#print axioms SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection_projection
#check @SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection_union
#print axioms SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection_union
#check @SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection_identity
#print axioms SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection_identity
#check @SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection_comparison
#print axioms SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection_comparison

#check @SerrePositivity.KST.SConstruction.flipFamily_evaluate
#print axioms SerrePositivity.KST.SConstruction.flipFamily_evaluate
#check @SerrePositivity.KST.SConstruction.normalizedPushoutSquareChoice
#print axioms SerrePositivity.KST.SConstruction.normalizedPushoutSquareChoice
#check @SerrePositivity.KST.SConstruction.normalizedPushoutSquareChoice_span
#print axioms SerrePositivity.KST.SConstruction.normalizedPushoutSquareChoice_span
#check @SerrePositivity.KST.SConstruction.normalizedPushoutSquareChoice_identity
#print axioms SerrePositivity.KST.SConstruction.normalizedPushoutSquareChoice_identity
#check @SerrePositivity.KST.SConstruction.chosenPushoutFamily
#print axioms SerrePositivity.KST.SConstruction.chosenPushoutFamily
#check @SerrePositivity.KST.SConstruction.chosenDiagramPushout
#print axioms SerrePositivity.KST.SConstruction.chosenDiagramPushout
#check @SerrePositivity.KST.SConstruction.chosenDiagramPushout_span
#print axioms SerrePositivity.KST.SConstruction.chosenDiagramPushout_span
#check @SerrePositivity.KST.SConstruction.chosenDiagramPushout_isPushout
#print axioms SerrePositivity.KST.SConstruction.chosenDiagramPushout_isPushout
#check @SerrePositivity.KST.SConstruction.chosenDiagramPushout_reindex
#print axioms SerrePositivity.KST.SConstruction.chosenDiagramPushout_reindex
#check @SerrePositivity.KST.SConstruction.chosenDiagramPushout_identity
#print axioms SerrePositivity.KST.SConstruction.chosenDiagramPushout_identity
#check @SerrePositivity.KST.SConstruction.selectedFunctorPushout
#print axioms SerrePositivity.KST.SConstruction.selectedFunctorPushout
#check @SerrePositivity.KST.SConstruction.selectedFunctorPushout_span
#print axioms SerrePositivity.KST.SConstruction.selectedFunctorPushout_span
#check @SerrePositivity.KST.SConstruction.selectedFunctorPushout_isPushout
#print axioms SerrePositivity.KST.SConstruction.selectedFunctorPushout_isPushout
#check @SerrePositivity.KST.SConstruction.selectedFunctorPushout_reindex
#print axioms SerrePositivity.KST.SConstruction.selectedFunctorPushout_reindex

#check @SerrePositivity.KST.SConstruction.exists_relative_zeroPrism
#print axioms SerrePositivity.KST.SConstruction.exists_relative_zeroPrism
#check @SerrePositivity.KST.SConstruction.zeroNaturalTransformation
#print axioms SerrePositivity.KST.SConstruction.zeroNaturalTransformation
#check @SerrePositivity.KST.SConstruction.zeroNaturalTransformation_zero
#print axioms SerrePositivity.KST.SConstruction.zeroNaturalTransformation_zero
#check @SerrePositivity.KST.SConstruction.zeroNaturalTransformation_one
#print axioms SerrePositivity.KST.SConstruction.zeroNaturalTransformation_one
#check @SerrePositivity.KST.SConstruction.zeroNaturalTransformation_fixed
#print axioms SerrePositivity.KST.SConstruction.zeroNaturalTransformation_fixed
#check @SerrePositivity.KST.SConstruction.zeroNaturalTransformation_constant
#print axioms SerrePositivity.KST.SConstruction.zeroNaturalTransformation_constant

#check @SerrePositivity.KST.SConstruction.isGapped_two_middle
#print axioms SerrePositivity.KST.SConstruction.isGapped_two_middle
#check @SerrePositivity.KST.SConstruction.sTwoCofiberRestriction
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberRestriction
#check @SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_ι
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_ι
#check @SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_vertex_surjective
#check @SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_hasLiftingProperty_boundary
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_hasLiftingProperty_boundary
#check @SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.cofiberDiagrams_quasicategory
#print axioms SerrePositivity.KST.SConstruction.cofiberDiagrams_quasicategory
#check @SerrePositivity.KST.SConstruction.cofiberDiagrams_isStable
#print axioms SerrePositivity.KST.SConstruction.cofiberDiagrams_isStable
#check @SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.cofiberStableModel
#print axioms SerrePositivity.KST.SConstruction.cofiberStableModel
#check @SerrePositivity.KST.SConstruction.sTwoCofiberComparison
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberComparison
#check @SerrePositivity.KST.SConstruction.sTwoCofiberSection
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberSection
#check @SerrePositivity.KST.SConstruction.sTwoCofiberSection_projection
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberSection_projection
#check @SerrePositivity.KST.SConstruction.sTwoCofiberSection_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberSection_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.sTwoCofiberInverse
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberInverse
#check @SerrePositivity.KST.SConstruction.sTwoCofiberSection_comparison
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberSection_comparison
#check @SerrePositivity.KST.SConstruction.sTwoCofiberEquivalence
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberEquivalence
#check @SerrePositivity.KST.SConstruction.sTwoCofiberComparison_realization_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberComparison_realization_localized_isIso

#check @SerrePositivity.KST.SConstruction.intervalMinOrder
#print axioms SerrePositivity.KST.SConstruction.intervalMinOrder
#check @SerrePositivity.KST.SConstruction.intervalMin
#print axioms SerrePositivity.KST.SConstruction.intervalMin
#check @SerrePositivity.KST.SConstruction.intervalMin_app_zero
#print axioms SerrePositivity.KST.SConstruction.intervalMin_app_zero
#check @SerrePositivity.KST.SConstruction.intervalMin_app_one
#print axioms SerrePositivity.KST.SConstruction.intervalMin_app_one
#check @SerrePositivity.KST.SConstruction.variableTimeShape
#print axioms SerrePositivity.KST.SConstruction.variableTimeShape
#check @SerrePositivity.KST.SConstruction.variableTimeShape_zero
#print axioms SerrePositivity.KST.SConstruction.variableTimeShape_zero
#check @SerrePositivity.KST.SConstruction.variableTimeShape_one
#print axioms SerrePositivity.KST.SConstruction.variableTimeShape_one
#check @SerrePositivity.KST.SConstruction.variableTimeImage
#print axioms SerrePositivity.KST.SConstruction.variableTimeImage
#check @SerrePositivity.KST.SConstruction.variableTimeImage_pre
#print axioms SerrePositivity.KST.SConstruction.variableTimeImage_pre
#check @SerrePositivity.KST.SConstruction.variableTimeImage_zero
#print axioms SerrePositivity.KST.SConstruction.variableTimeImage_zero
#check @SerrePositivity.KST.SConstruction.variableTimeImage_one
#print axioms SerrePositivity.KST.SConstruction.variableTimeImage_one
#check @SerrePositivity.KST.SConstruction.variableTimeHomotopy
#print axioms SerrePositivity.KST.SConstruction.variableTimeHomotopy
#check @SerrePositivity.KST.SConstruction.variableTimeHomotopy_isInvertible
#print axioms SerrePositivity.KST.SConstruction.variableTimeHomotopy_isInvertible
#check @SerrePositivity.KST.SConstruction.variableTimeImageIso
#print axioms SerrePositivity.KST.SConstruction.variableTimeImageIso
#check @SerrePositivity.KST.SConstruction.IsGapped.variableTimeImage
#print axioms SerrePositivity.KST.SConstruction.IsGapped.variableTimeImage
#check @SerrePositivity.KST.SConstruction.gappedObjectVertex
#print axioms SerrePositivity.KST.SConstruction.gappedObjectVertex
#check @SerrePositivity.KST.SConstruction.gappedDiagram_gappedObjectVertex
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_gappedObjectVertex
#check @SerrePositivity.KST.SConstruction.gappedDiagram_injective
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_injective
#check @SerrePositivity.KST.SConstruction.gappedDiagram_sMap
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_sMap
#check @SerrePositivity.KST.SConstruction.gappedDiagram_objectS_map
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_objectS_map
#check @SerrePositivity.KST.SConstruction.gappedDiagram_sPostcompCofiber
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_sPostcompCofiber
#check @SerrePositivity.KST.SConstruction.gappedDiagram_objectSFunctor_map
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_objectSFunctor_map
#check @SerrePositivity.KST.SConstruction.arFirstEndpointOrder
#print axioms SerrePositivity.KST.SConstruction.arFirstEndpointOrder
#check @SerrePositivity.KST.SConstruction.arFirstEndpoint
#print axioms SerrePositivity.KST.SConstruction.arFirstEndpoint
#check @SerrePositivity.KST.SConstruction.arTimeCoordinate
#print axioms SerrePositivity.KST.SConstruction.arTimeCoordinate
#check @SerrePositivity.KST.SConstruction.arTimeCoordinate_naturality
#print axioms SerrePositivity.KST.SConstruction.arTimeCoordinate_naturality
#check @SerrePositivity.KST.SConstruction.arTimeCoordinate_constant
#print axioms SerrePositivity.KST.SConstruction.arTimeCoordinate_constant
#check @SerrePositivity.KST.SConstruction.objectSHomotopyVertex
#print axioms SerrePositivity.KST.SConstruction.objectSHomotopyVertex
#check @SerrePositivity.KST.SConstruction.objectSHomotopyVertex_diagram
#print axioms SerrePositivity.KST.SConstruction.objectSHomotopyVertex_diagram
#check @SerrePositivity.KST.SConstruction.objectSHomotopyMap
#print axioms SerrePositivity.KST.SConstruction.objectSHomotopyMap
#check @SerrePositivity.KST.SConstruction.objectSHomotopy
#print axioms SerrePositivity.KST.SConstruction.objectSHomotopy
#check @SerrePositivity.KST.SConstruction.objectSHomotopyOfFunctorIso
#print axioms SerrePositivity.KST.SConstruction.objectSHomotopyOfFunctorIso
#check @SerrePositivity.KST.SConstruction.preservesSConstructionData_section_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.preservesSConstructionData_section_of_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.objectS_map_isSimplicialHomotopyEquivalence_of_inverse
#print axioms SerrePositivity.KST.SConstruction.objectS_map_isSimplicialHomotopyEquivalence_of_inverse
#check @SerrePositivity.KST.SConstruction.objectS_map_isSimplicialHomotopyEquivalence_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.objectS_map_isSimplicialHomotopyEquivalence_of_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.objectS_map_localized_isIso_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.objectS_map_localized_isIso_of_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.sTwoCofiberComparison_objectS_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberComparison_objectS_localized_isIso

#check @SerrePositivity.KST.SConstruction.IsEquivalenceDiagramVertex
#print axioms SerrePositivity.KST.SConstruction.IsEquivalenceDiagramVertex
#check @SerrePositivity.KST.SConstruction.equivalenceDiagrams
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagrams
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramι
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramι
#check @SerrePositivity.KST.SConstruction.equivalenceDiagrams_quasicategory
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagrams_quasicategory
#check @SerrePositivity.KST.SConstruction.isEquivalenceDiagramVertex_functorVertex
#print axioms SerrePositivity.KST.SConstruction.isEquivalenceDiagramVertex_functorVertex
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramReindex
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramReindex
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramReindex_ι
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramReindex_ι
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluation
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluation
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramConstant
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramConstant
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramConstant_ι
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramConstant_ι
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramConstant_evaluation
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramConstant_evaluation
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramReindex_id
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramReindex_id
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramReindex_comp
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramReindex_comp
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramReindex_evaluation
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramReindex_evaluation
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramConstant_reindex
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramConstant_reindex
#check @SerrePositivity.KST.SConstruction.simplicialEquivalenceDiagrams
#print axioms SerrePositivity.KST.SConstruction.simplicialEquivalenceDiagrams
#check @SerrePositivity.KST.SConstruction.constantEquivalenceDiagramNat
#print axioms SerrePositivity.KST.SConstruction.constantEquivalenceDiagramNat
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramVertexOfCoreMap
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramVertexOfCoreMap
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramCoreMap
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramCoreMap
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramVerticesEquiv
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramVerticesEquiv
#check @SerrePositivity.KST.SConstruction.pointFunctorEvaluationIso
#print axioms SerrePositivity.KST.SConstruction.pointFunctorEvaluationIso
#check @SerrePositivity.KST.SConstruction.evaluateFunctorAt_factor
#print axioms SerrePositivity.KST.SConstruction.evaluateFunctorAt_factor
#check @SerrePositivity.KST.SConstruction.evaluateFunctorAt_innerFibration
#print axioms SerrePositivity.KST.SConstruction.evaluateFunctorAt_innerFibration
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluation_innerFibration
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluation_innerFibration
#check @SerrePositivity.KST.SConstruction.zeroEquivalenceDiagramEvaluationIso
#print axioms SerrePositivity.KST.SConstruction.zeroEquivalenceDiagramEvaluationIso
#check @SerrePositivity.KST.SConstruction.zeroEquivalenceDiagramEvaluation_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroEquivalenceDiagramEvaluation_isIso
#check @SerrePositivity.KST.SConstruction.simplexInitialOrder
#print axioms SerrePositivity.KST.SConstruction.simplexInitialOrder
#check @SerrePositivity.KST.SConstruction.simplexInitialContraction
#print axioms SerrePositivity.KST.SConstruction.simplexInitialContraction
#check @SerrePositivity.KST.SConstruction.simplexInitialContraction_zero
#print axioms SerrePositivity.KST.SConstruction.simplexInitialContraction_zero
#check @SerrePositivity.KST.SConstruction.simplexInitialContraction_one
#print axioms SerrePositivity.KST.SConstruction.simplexInitialContraction_one
#check @SerrePositivity.KST.SConstruction.simplexInitialContraction_firstVertex
#print axioms SerrePositivity.KST.SConstruction.simplexInitialContraction_firstVertex
#check @SerrePositivity.KST.SConstruction.restrictedPrecompositionIso
#print axioms SerrePositivity.KST.SConstruction.restrictedPrecompositionIso
#check @SerrePositivity.KST.SConstruction.pre_constant_evaluation
#print axioms SerrePositivity.KST.SConstruction.pre_constant_evaluation
#check @SerrePositivity.KST.SConstruction.simplexInitialHomotopy
#print axioms SerrePositivity.KST.SConstruction.simplexInitialHomotopy
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluation_comparison
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluation_comparison
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluationEquivalence
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluationEquivalence
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluation_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluation_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.equivalenceDiagrams_isStable
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagrams_isStable
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramStableModel
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramStableModel
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramStableEvaluation
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramStableEvaluation
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramStableConstant
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramStableConstant
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramStableConstant_evaluation
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramStableConstant_evaluation
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramStableEvaluation_objectS_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramStableEvaluation_objectS_localized_isIso
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramStableConstant_objectS_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramStableConstant_objectS_localized_isIso
#check @SerrePositivity.KST.SConstruction.PreservesSConstructionData.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.PreservesSConstructionData.of_functorIso
#check @SerrePositivity.KST.SConstruction.evaluateFunctorAt_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.evaluateFunctorAt_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.constantFunctor_evaluation
#print axioms SerrePositivity.KST.SConstruction.constantFunctor_evaluation
#check @SerrePositivity.KST.SConstruction.constantFunctor_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.constantFunctor_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramι_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramι_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.isGapped_functor_iff_pointwise
#print axioms SerrePositivity.KST.SConstruction.isGapped_functor_iff_pointwise
#check @SerrePositivity.KST.SConstruction.isGapped_equivalenceDiagramι_iff
#print axioms SerrePositivity.KST.SConstruction.isGapped_equivalenceDiagramι_iff
#check @SerrePositivity.KST.SConstruction.diagramSpace_quasicategory
#print axioms SerrePositivity.KST.SConstruction.diagramSpace_quasicategory
#check @SerrePositivity.KST.SConstruction.gappedFamilyLift
#print axioms SerrePositivity.KST.SConstruction.gappedFamilyLift
#check @SerrePositivity.KST.SConstruction.gappedFamilyLift_ι
#print axioms SerrePositivity.KST.SConstruction.gappedFamilyLift_ι
#check @SerrePositivity.KST.SConstruction.coreGappedFamilyLift
#print axioms SerrePositivity.KST.SConstruction.coreGappedFamilyLift
#check @SerrePositivity.KST.SConstruction.coreGappedFamilyLift_ι
#print axioms SerrePositivity.KST.SConstruction.coreGappedFamilyLift_ι
#check @SerrePositivity.KST.SConstruction.flipFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.flipFamily_vertex
#check @SerrePositivity.KST.SConstruction.isInvertibleFunctorEdge_iff_pointwise
#print axioms SerrePositivity.KST.SConstruction.isInvertibleFunctorEdge_iff_pointwise
#check @SerrePositivity.KST.SConstruction.flipEquivalenceDiagram_edge
#print axioms SerrePositivity.KST.SConstruction.flipEquivalenceDiagram_edge
#check @SerrePositivity.KST.SConstruction.flipGappedEquivalenceDiagram_vertex
#print axioms SerrePositivity.KST.SConstruction.flipGappedEquivalenceDiagram_vertex
#check @SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramCoreMap
#print axioms SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramCoreMap
#check @SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramCoreMap_ι
#print axioms SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramCoreMap_ι
#check @SerrePositivity.KST.SConstruction.flipCoreGappedFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.flipCoreGappedFamily_vertex
#check @SerrePositivity.KST.SConstruction.coreGappedEquivalenceDiagram
#print axioms SerrePositivity.KST.SConstruction.coreGappedEquivalenceDiagram
#check @SerrePositivity.KST.SConstruction.coreGappedEquivalenceDiagram_ι
#print axioms SerrePositivity.KST.SConstruction.coreGappedEquivalenceDiagram_ι
#check @SerrePositivity.KST.SConstruction.coreGappedEquivalenceDiagram_isGapped
#print axioms SerrePositivity.KST.SConstruction.coreGappedEquivalenceDiagram_isGapped
#check @SerrePositivity.KST.SConstruction.coreGappedEquivalenceDiagramVertex
#print axioms SerrePositivity.KST.SConstruction.coreGappedEquivalenceDiagramVertex
#check @SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramVerticesEquiv
#print axioms SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramVerticesEquiv
#check @SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramCoreMap_sMap
#print axioms SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramCoreMap_sMap
#check @SerrePositivity.KST.SConstruction.objectCoreRowIso
#print axioms SerrePositivity.KST.SConstruction.objectCoreRowIso
#check @SerrePositivity.KST.SConstruction.objectRowInclusion
#print axioms SerrePositivity.KST.SConstruction.objectRowInclusion
#check @SerrePositivity.KST.SConstruction.objectRowsInclusion
#print axioms SerrePositivity.KST.SConstruction.objectRowsInclusion
#check @SerrePositivity.KST.SConstruction.diagonalFlipIso
#print axioms SerrePositivity.KST.SConstruction.diagonalFlipIso
#check @SerrePositivity.KST.SConstruction.diagonalConstIso
#print axioms SerrePositivity.KST.SConstruction.diagonalConstIso
#check @SerrePositivity.KST.SConstruction.objectRowsInclusion_diagonal
#print axioms SerrePositivity.KST.SConstruction.objectRowsInclusion_diagonal
#check @SerrePositivity.KST.SConstruction.flipConstantFamily
#print axioms SerrePositivity.KST.SConstruction.flipConstantFamily
#check @SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramCoreMap_constant
#print axioms SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramCoreMap_constant
#check @SerrePositivity.KST.SConstruction.objectCoreRowIso_constant
#print axioms SerrePositivity.KST.SConstruction.objectCoreRowIso_constant
#check @SerrePositivity.KST.SConstruction.objectRowInclusion_coreS_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.objectRowInclusion_coreS_localized_isIso
#check @SerrePositivity.KST.SConstruction.diagonalObjectInclusion_coreS_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.diagonalObjectInclusion_coreS_localized_isIso
#check @SerrePositivity.KST.SConstruction.objectToCoreSRealization_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.objectToCoreSRealization_localized_isIso
#check @SerrePositivity.KST.SConstruction.zeroCofiberSquare
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberSquare
#check @SerrePositivity.KST.SConstruction.zeroCofiberSquare_evaluation
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberSquare_evaluation
#check @SerrePositivity.KST.SConstruction.zeroCofiberSquare_vertex_isPushout
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberSquare_vertex_isPushout
#check @SerrePositivity.KST.SConstruction.zeroCofiberFunctor
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberFunctor
#check @SerrePositivity.KST.SConstruction.zeroCofiberFunctor_ι
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberFunctor_ι
#check @SerrePositivity.KST.SConstruction.zeroCofiberFunctor_input_evaluation
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberFunctor_input_evaluation
#check @SerrePositivity.KST.SConstruction.zeroCofiberFunctor_quotient
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberFunctor_quotient
#check @SerrePositivity.KST.SConstruction.constantZero_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.constantZero_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.preservesSConstructionData_functor_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.preservesSConstructionData_functor_of_pointwise
#check @SerrePositivity.KST.SConstruction.preservesSConstructionData_of_comp_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.preservesSConstructionData_of_comp_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.zeroCofiberFunctor_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberFunctor_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.pre_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.pre_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.cofiberInclusion_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.cofiberInclusion_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.cofiberEvaluation_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.cofiberEvaluation_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.cofiberStableEvaluation
#print axioms SerrePositivity.KST.SConstruction.cofiberStableEvaluation
#check @SerrePositivity.KST.SConstruction.cofiberStableSubobject
#print axioms SerrePositivity.KST.SConstruction.cofiberStableSubobject
#check @SerrePositivity.KST.SConstruction.cofiberStableMiddle
#print axioms SerrePositivity.KST.SConstruction.cofiberStableMiddle
#check @SerrePositivity.KST.SConstruction.cofiberStableQuotient
#print axioms SerrePositivity.KST.SConstruction.cofiberStableQuotient
#check @SerrePositivity.KST.SConstruction.zeroCofiberStableFunctor
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberStableFunctor
#check @SerrePositivity.KST.SConstruction.zeroCofiberStableFunctor_subobject
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberStableFunctor_subobject
#check @SerrePositivity.KST.SConstruction.zeroCofiberStableFunctor_quotient
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberStableFunctor_quotient
#check @SerrePositivity.KST.SConstruction.simplexLeftFiber
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiber
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberProjection
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberProjection
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberParameter
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberParameter
#check @SerrePositivity.KST.SConstruction.simplexLeftFiber_condition
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiber_condition
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberLift
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberLift
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberLift_projection
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberLift_projection
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberLift_parameter
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberLift_parameter
#check @SerrePositivity.KST.SConstruction.simplexLeftFiber_hom_ext
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiber_hom_ext
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberMap
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberMap
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberMap_projection
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberMap_projection
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberMap_parameter
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberMap_parameter
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberSimplexEquiv
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberSimplexEquiv
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberMap_postcomp
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberMap_postcomp
#check @SerrePositivity.KST.SConstruction.cofiberSubobjectLeftFiber
#print axioms SerrePositivity.KST.SConstruction.cofiberSubobjectLeftFiber
#check @SerrePositivity.KST.SConstruction.cofiberLeftFiberQuotient
#print axioms SerrePositivity.KST.SConstruction.cofiberLeftFiberQuotient
#check @SerrePositivity.KST.SConstruction.arNerveMap_const
#print axioms SerrePositivity.KST.SConstruction.arNerveMap_const
#check @SerrePositivity.KST.SConstruction.gappedDiagram_objectS_const
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_objectS_const
#check @SerrePositivity.KST.SConstruction.objectSLastDiagonalZeroVertex
#print axioms SerrePositivity.KST.SConstruction.objectSLastDiagonalZeroVertex
#check @SerrePositivity.KST.SConstruction.stableConstantZero
#print axioms SerrePositivity.KST.SConstruction.stableConstantZero
#check @SerrePositivity.KST.SConstruction.objectS_lastVertex_constantZero
#print axioms SerrePositivity.KST.SConstruction.objectS_lastVertex_constantZero
#check @SerrePositivity.KST.SConstruction.zeroCofiberStableFunctor_subobject_true
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberStableFunctor_subobject_true
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberSection
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberSection
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberSection_projection
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberSection_projection
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberSection_parameter
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberSection_parameter
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberSection_quotient
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberSection_quotient
#check @SerrePositivity.KST.SConstruction.orderPrismOrder
#print axioms SerrePositivity.KST.SConstruction.orderPrismOrder
#check @SerrePositivity.KST.SConstruction.orderPrism
#print axioms SerrePositivity.KST.SConstruction.orderPrism
#check @SerrePositivity.KST.SConstruction.orderPrism_zero
#print axioms SerrePositivity.KST.SConstruction.orderPrism_zero
#check @SerrePositivity.KST.SConstruction.orderPrism_one
#print axioms SerrePositivity.KST.SConstruction.orderPrism_one
#check @SerrePositivity.KST.SConstruction.orderPrism_pre
#print axioms SerrePositivity.KST.SConstruction.orderPrism_pre
#check @SerrePositivity.KST.SConstruction.orderPrism_post
#print axioms SerrePositivity.KST.SConstruction.orderPrism_post
#check @SerrePositivity.KST.SConstruction.orderPrism_refl
#print axioms SerrePositivity.KST.SConstruction.orderPrism_refl
#check @SerrePositivity.KST.SConstruction.orderPrism_of_eq
#print axioms SerrePositivity.KST.SConstruction.orderPrism_of_eq
#check @SerrePositivity.KST.SConstruction.mcCarthyMovedOrder
#print axioms SerrePositivity.KST.SConstruction.mcCarthyMovedOrder
#check @SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_le
#print axioms SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_le
#check @SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_comp
#print axioms SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_comp
#check @SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_zero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_zero
#check @SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_one
#print axioms SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_one
#check @SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_simplex
#print axioms SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_simplex
#check @SerrePositivity.KST.SConstruction.mcCarthyArMotion
#print axioms SerrePositivity.KST.SConstruction.mcCarthyArMotion
#check @SerrePositivity.KST.SConstruction.mcCarthyArMotion_zero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyArMotion_zero
#check @SerrePositivity.KST.SConstruction.mcCarthyArMotion_one
#print axioms SerrePositivity.KST.SConstruction.mcCarthyArMotion_one
#check @SerrePositivity.KST.SConstruction.mcCarthyArMotion_pre
#print axioms SerrePositivity.KST.SConstruction.mcCarthyArMotion_pre
#check @SerrePositivity.KST.SConstruction.mcCarthyArMotion_timeZero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyArMotion_timeZero
#check @SerrePositivity.KST.SConstruction.mcCarthyLambda
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambda
#check @SerrePositivity.KST.SConstruction.mcCarthyMu
#print axioms SerrePositivity.KST.SConstruction.mcCarthyMu
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaMu
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaMu
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_zero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_zero
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_one
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_one
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_pre
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_pre
#check @SerrePositivity.KST.SConstruction.mcCarthyLambda_isGapped
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambda_isGapped
#check @SerrePositivity.KST.SConstruction.mcCarthyMu_isGapped
#print axioms SerrePositivity.KST.SConstruction.mcCarthyMu_isGapped
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_timeZero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_timeZero
#check @SerrePositivity.KST.SConstruction.exists_lift_prism_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.exists_lift_prism_of_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.liftPrismOfTrivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.liftPrismOfTrivialKanFibration
#check @SerrePositivity.KST.SConstruction.liftPrismOfTrivialKanFibration_zero
#print axioms SerrePositivity.KST.SConstruction.liftPrismOfTrivialKanFibration_zero
#check @SerrePositivity.KST.SConstruction.liftPrismOfTrivialKanFibration_one
#print axioms SerrePositivity.KST.SConstruction.liftPrismOfTrivialKanFibration_one
#check @SerrePositivity.KST.SConstruction.liftPrismOfTrivialKanFibration_projection
#print axioms SerrePositivity.KST.SConstruction.liftPrismOfTrivialKanFibration_projection
#check @SerrePositivity.KST.SConstruction.arrowSourcePrism
#print axioms SerrePositivity.KST.SConstruction.arrowSourcePrism
#check @SerrePositivity.KST.SConstruction.arrowSourcePrism_zero
#print axioms SerrePositivity.KST.SConstruction.arrowSourcePrism_zero
#check @SerrePositivity.KST.SConstruction.arrowSourcePrism_one
#print axioms SerrePositivity.KST.SConstruction.arrowSourcePrism_one
#check @SerrePositivity.KST.SConstruction.arrowSourcePrism_source
#print axioms SerrePositivity.KST.SConstruction.arrowSourcePrism_source
#check @SerrePositivity.KST.SConstruction.zeroCofiberFunctor_identityProjection
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberFunctor_identityProjection
#check @SerrePositivity.KST.SConstruction.cofiberLambdaNu
#print axioms SerrePositivity.KST.SConstruction.cofiberLambdaNu
#check @SerrePositivity.KST.SConstruction.cofiberLambdaNu_zero
#print axioms SerrePositivity.KST.SConstruction.cofiberLambdaNu_zero
#check @SerrePositivity.KST.SConstruction.cofiberLambdaNu_one
#print axioms SerrePositivity.KST.SConstruction.cofiberLambdaNu_one
#check @SerrePositivity.KST.SConstruction.cofiberLambdaNu_projection
#print axioms SerrePositivity.KST.SConstruction.cofiberLambdaNu_projection
#check @SerrePositivity.KST.SConstruction.cofiberLambdaNu_source
#print axioms SerrePositivity.KST.SConstruction.cofiberLambdaNu_source
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaNu
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaNu
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaNu_pre
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaNu_pre
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaNu_zero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaNu_zero
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaNu_one
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaNu_one
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaNu_source
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaNu_source
#check @SerrePositivity.KST.SConstruction.spanPrism_source
#print axioms SerrePositivity.KST.SConstruction.spanPrism_source
#check @SerrePositivity.KST.SConstruction.spanPrisms_isPushout
#print axioms SerrePositivity.KST.SConstruction.spanPrisms_isPushout
#check @SerrePositivity.KST.SConstruction.spanPrisms
#print axioms SerrePositivity.KST.SConstruction.spanPrisms
#check @SerrePositivity.KST.SConstruction.spanPrisms_left
#print axioms SerrePositivity.KST.SConstruction.spanPrisms_left
#check @SerrePositivity.KST.SConstruction.spanPrisms_right
#print axioms SerrePositivity.KST.SConstruction.spanPrisms_right
#check @SerrePositivity.KST.SConstruction.spanPrisms_hom_ext
#print axioms SerrePositivity.KST.SConstruction.spanPrisms_hom_ext
#check @SerrePositivity.KST.SConstruction.spanPrisms_post
#print axioms SerrePositivity.KST.SConstruction.spanPrisms_post
#check @SerrePositivity.KST.SConstruction.spanPrisms_pre
#print axioms SerrePositivity.KST.SConstruction.spanPrisms_pre
#check @SerrePositivity.KST.SConstruction.spanPrisms_constant_left
#print axioms SerrePositivity.KST.SConstruction.spanPrisms_constant_left
#check @SerrePositivity.KST.SConstruction.mcCarthySpan
#print axioms SerrePositivity.KST.SConstruction.mcCarthySpan
#check @SerrePositivity.KST.SConstruction.mcCarthySpan_upper
#print axioms SerrePositivity.KST.SConstruction.mcCarthySpan_upper
#check @SerrePositivity.KST.SConstruction.mcCarthySpan_left
#print axioms SerrePositivity.KST.SConstruction.mcCarthySpan_left
#check @SerrePositivity.KST.SConstruction.mcCarthySpan_pre
#print axioms SerrePositivity.KST.SConstruction.mcCarthySpan_pre
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_source
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_source
#check @SerrePositivity.KST.SConstruction.mcCarthySpan_timeZero
#print axioms SerrePositivity.KST.SConstruction.mcCarthySpan_timeZero
#check @SerrePositivity.KST.SConstruction.exchangeFirstTwo
#print axioms SerrePositivity.KST.SConstruction.exchangeFirstTwo
#check @SerrePositivity.KST.SConstruction.exchangeFirstTwo_naturality
#print axioms SerrePositivity.KST.SConstruction.exchangeFirstTwo_naturality
#check @SerrePositivity.KST.SConstruction.exchangeDiagramFamily
#print axioms SerrePositivity.KST.SConstruction.exchangeDiagramFamily
#check @SerrePositivity.KST.SConstruction.exchangeDiagramFamily_pre
#print axioms SerrePositivity.KST.SConstruction.exchangeDiagramFamily_pre
#check @SerrePositivity.KST.SConstruction.exchangeFirstTwo_naturality_left
#print axioms SerrePositivity.KST.SConstruction.exchangeFirstTwo_naturality_left
#check @SerrePositivity.KST.SConstruction.exchangeDiagramFamily_pre_left
#print axioms SerrePositivity.KST.SConstruction.exchangeDiagramFamily_pre_left
#check @SerrePositivity.KST.SConstruction.exchangeDiagramFamily_evaluation_interval
#print axioms SerrePositivity.KST.SConstruction.exchangeDiagramFamily_evaluation_interval
#check @SerrePositivity.KST.SConstruction.pointwisePushoutApex
#print axioms SerrePositivity.KST.SConstruction.pointwisePushoutApex
#check @SerrePositivity.KST.SConstruction.pointwisePushoutApex_pre
#print axioms SerrePositivity.KST.SConstruction.pointwisePushoutApex_pre
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex_pre
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex_pre
#check @SerrePositivity.KST.SConstruction.pointwisePushoutApex_identity
#print axioms SerrePositivity.KST.SConstruction.pointwisePushoutApex_identity
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex_identity
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex_identity
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoRaw
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoRaw
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_pre
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_pre
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_timeZero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_timeZero

#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushout
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushout
#check @SerrePositivity.KST.SConstruction.ihomCurry_evaluate_pair
#print axioms SerrePositivity.KST.SConstruction.ihomCurry_evaluate_pair
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushout_evaluate
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushout_evaluate
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushout_isPushout
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushout_isPushout
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushout_span
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushout_span
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushout_apex
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushout_apex
#check @SerrePositivity.KST.SConstruction.chosenDiagramPushout_apex
#print axioms SerrePositivity.KST.SConstruction.chosenDiagramPushout_apex
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex_postcompIso
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex_postcompIso
#check @SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex.of_vertexIso
#print axioms SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex.of_vertexIso
#check @SerrePositivity.KST.SConstruction.pointwiseCofiberPushout_vertex
#print axioms SerrePositivity.KST.SConstruction.pointwiseCofiberPushout_vertex
#check @SerrePositivity.KST.SConstruction.pointwiseCofiberPushout
#print axioms SerrePositivity.KST.SConstruction.pointwiseCofiberPushout
#check @SerrePositivity.KST.SConstruction.pointwiseCofiberPushout_ι
#print axioms SerrePositivity.KST.SConstruction.pointwiseCofiberPushout_ι
#check @SerrePositivity.KST.SConstruction.pointwisePushoutApex_isGapped
#print axioms SerrePositivity.KST.SConstruction.pointwisePushoutApex_isGapped
#check @SerrePositivity.KST.SConstruction.pointwiseCofiberPushout_iso
#print axioms SerrePositivity.KST.SConstruction.pointwiseCofiberPushout_iso
#check @SerrePositivity.KST.SConstruction.pointwiseCofiberPushout_isGapped
#print axioms SerrePositivity.KST.SConstruction.pointwiseCofiberPushout_isGapped
#check @SerrePositivity.KST.SConstruction.transposeFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.transposeFamily_vertex
#check @SerrePositivity.KST.SConstruction.transposeFamily_interval_vertex
#print axioms SerrePositivity.KST.SConstruction.transposeFamily_interval_vertex
#check @SerrePositivity.KST.SConstruction.mcCarthySpan_isGapped_vertex
#print axioms SerrePositivity.KST.SConstruction.mcCarthySpan_isGapped_vertex
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_isCofiber
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_isCofiber
#check @SerrePositivity.KST.SConstruction.mcCarthyRho
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRho
#check @SerrePositivity.KST.SConstruction.mcCarthyRho_ι
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRho_ι
#check @SerrePositivity.KST.SConstruction.mcCarthyRho_timeZero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRho_timeZero
#check @SerrePositivity.KST.SConstruction.mcCarthyRho_pre
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRho_pre
#check @SerrePositivity.KST.SConstruction.mcCarthyRho_isGapped
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRho_isGapped
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_isGapped
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_isGapped

#check @SerrePositivity.KST.SConstruction.exchangeDiagramFamily_evaluate
#print axioms SerrePositivity.KST.SConstruction.exchangeDiagramFamily_evaluate
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex_evaluate
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex_evaluate
#check @SerrePositivity.KST.SConstruction.curry_identitySpan
#print axioms SerrePositivity.KST.SConstruction.curry_identitySpan
#check @SerrePositivity.KST.SConstruction.spanFamily_constant_right
#print axioms SerrePositivity.KST.SConstruction.spanFamily_constant_right
#check @SerrePositivity.KST.SConstruction.spanFamily_constant_left
#print axioms SerrePositivity.KST.SConstruction.spanFamily_constant_left
#check @SerrePositivity.KST.SConstruction.cofiberProjection_source
#print axioms SerrePositivity.KST.SConstruction.cofiberProjection_source
#check @SerrePositivity.KST.SConstruction.mcCarthySpan_source
#print axioms SerrePositivity.KST.SConstruction.mcCarthySpan_source
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_quotient
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_quotient
#check @SerrePositivity.KST.SConstruction.mcCarthySpan_quotient
#print axioms SerrePositivity.KST.SConstruction.mcCarthySpan_quotient
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_source
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_source
#check @SerrePositivity.KST.SConstruction.mcCarthyRho_source
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRho_source
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_quotient
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_quotient
#check @SerrePositivity.KST.SConstruction.mcCarthyRho_quotient
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRho_quotient
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberDiagram
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberDiagram
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberParameter
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberParameter
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberDiagram_source
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberDiagram_source
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberDiagram_map
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberDiagram_map
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberParameter_map
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberParameter_map
#check @SerrePositivity.KST.SConstruction.simplexOrder_map
#print axioms SerrePositivity.KST.SConstruction.simplexOrder_map
#check @SerrePositivity.KST.SConstruction.mcCarthyRho_congr
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRho_congr
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberObjectVertex
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberObjectVertex
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberObjectVertex_diagram
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberObjectVertex_diagram
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberObjectMap
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberObjectMap
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberParameterMap
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberParameterMap
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiber_condition
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiber_condition
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap_projection
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap_projection
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap_parameter
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap_parameter
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberObjectMap_zero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberObjectMap_zero
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberParameterMap_endpoint
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberParameterMap_endpoint
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap_zero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap_zero
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoTerminal
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoTerminal
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberHomotopy
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberHomotopy
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap_quotient
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap_quotient
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoTerminal_parameter
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoTerminal_parameter
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoTerminal_quotient
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoTerminal_quotient
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoTerminal_source
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoTerminal_source

#check @SerrePositivity.KST.SConstruction.exists_relative_initialPrism
#print axioms SerrePositivity.KST.SConstruction.exists_relative_initialPrism
#check @SerrePositivity.KST.SConstruction.fixedSourceArrows
#print axioms SerrePositivity.KST.SConstruction.fixedSourceArrows
#check @SerrePositivity.KST.SConstruction.fixedSourceArrowsι
#print axioms SerrePositivity.KST.SConstruction.fixedSourceArrowsι
#check @SerrePositivity.KST.SConstruction.fixedSourceArrowsTarget
#print axioms SerrePositivity.KST.SConstruction.fixedSourceArrowsTarget
#check @SerrePositivity.KST.SConstruction.fixedSourceArrowsι_source
#print axioms SerrePositivity.KST.SConstruction.fixedSourceArrowsι_source
#check @SerrePositivity.KST.SConstruction.fixedSourceArrowsTarget_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.fixedSourceArrowsTarget_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibers
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibers
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersι
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersι
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersι_source
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersι_source
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersQuotient
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersQuotient
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersInput
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersInput
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersInput_ι
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersInput_ι
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersCanonical
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersCanonical
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersCanonical_source
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersCanonical_source
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersCanonicalInput
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersCanonicalInput
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersCanonicalInput_ι
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersCanonicalInput_ι
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism_zero
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism_zero
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism_one
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism_one
#check @SerrePositivity.KST.SConstruction.zeroSourceThetaInput
#print axioms SerrePositivity.KST.SConstruction.zeroSourceThetaInput
#check @SerrePositivity.KST.SConstruction.zeroSourceThetaInput_zero
#print axioms SerrePositivity.KST.SConstruction.zeroSourceThetaInput_zero
#check @SerrePositivity.KST.SConstruction.zeroSourceThetaInput_one
#print axioms SerrePositivity.KST.SConstruction.zeroSourceThetaInput_one
#check @SerrePositivity.KST.SConstruction.zeroSourceThetaInput_target
#print axioms SerrePositivity.KST.SConstruction.zeroSourceThetaInput_target
#check @SerrePositivity.KST.SConstruction.zeroSourceTheta
#print axioms SerrePositivity.KST.SConstruction.zeroSourceTheta
#check @SerrePositivity.KST.SConstruction.zeroSourceTheta_zero
#print axioms SerrePositivity.KST.SConstruction.zeroSourceTheta_zero
#check @SerrePositivity.KST.SConstruction.zeroSourceTheta_one
#print axioms SerrePositivity.KST.SConstruction.zeroSourceTheta_one
#check @SerrePositivity.KST.SConstruction.zeroSourceTheta_projection
#print axioms SerrePositivity.KST.SConstruction.zeroSourceTheta_projection
#check @SerrePositivity.KST.SConstruction.zeroSourceTheta_source
#print axioms SerrePositivity.KST.SConstruction.zeroSourceTheta_source
#check @SerrePositivity.KST.SConstruction.uncurry_vertex_restriction
#print axioms SerrePositivity.KST.SConstruction.uncurry_vertex_restriction
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism_vertex
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism_vertex
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersRight_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersRight_isIso
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism_isInvertible
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism_isInvertible
#check @SerrePositivity.KST.SConstruction.zeroSourceThetaInput_isInvertible
#print axioms SerrePositivity.KST.SConstruction.zeroSourceThetaInput_isInvertible
#check @SerrePositivity.KST.SConstruction.zeroSourceTheta_isInvertible
#print axioms SerrePositivity.KST.SConstruction.zeroSourceTheta_isInvertible
#check @SerrePositivity.KST.SConstruction.zeroSourceThetaHomotopy
#print axioms SerrePositivity.KST.SConstruction.zeroSourceThetaHomotopy
#check @SerrePositivity.KST.SConstruction.zeroSourceThetaHomotopy_isInvertible
#print axioms SerrePositivity.KST.SConstruction.zeroSourceThetaHomotopy_isInvertible
#check @SerrePositivity.KST.SConstruction.zeroSourceTheta_variableTime_isGapped
#print axioms SerrePositivity.KST.SConstruction.zeroSourceTheta_variableTime_isGapped
#check @SerrePositivity.KST.SConstruction.zeroSourceTheta_variableTime_source
#print axioms SerrePositivity.KST.SConstruction.zeroSourceTheta_variableTime_source
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram_ι
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram_ι
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram_map
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram_map
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram_isGapped
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram_isGapped
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaObjectVertex
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaObjectVertex
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaObjectVertex_diagram
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaObjectVertex_diagram
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaObjectMap
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaObjectMap
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaFiber_condition
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaFiber_condition
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap_projection
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap_projection
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap_parameter
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap_parameter
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram_quotient
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram_quotient
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaObjectMap_zero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaObjectMap_zero
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaObjectMap_one
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaObjectMap_one
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap_zero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap_zero
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap_one
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap_one
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaFiberHomotopy
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaFiberHomotopy
#check @SerrePositivity.KST.SConstruction.mcCarthyFiber_retraction_localized
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiber_retraction_localized
#check @SerrePositivity.KST.SConstruction.cofiberLeftFiberQuotient_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.cofiberLeftFiberQuotient_localized_isIso

#check @SerrePositivity.KST.SConstruction.simplexFiberDiagramMap
#print axioms SerrePositivity.KST.SConstruction.simplexFiberDiagramMap

#check @SerrePositivity.KST.SConstruction.simplexFiberDiagramMap_projection
#print axioms SerrePositivity.KST.SConstruction.simplexFiberDiagramMap_projection

#check @SerrePositivity.KST.SConstruction.simplexFiberDiagramMap_parameter
#print axioms SerrePositivity.KST.SConstruction.simplexFiberDiagramMap_parameter

#check @SerrePositivity.KST.SConstruction.simplexFiberDiagram
#print axioms SerrePositivity.KST.SConstruction.simplexFiberDiagram

#check @SerrePositivity.KST.SConstruction.simplexFiberProjection
#print axioms SerrePositivity.KST.SConstruction.simplexFiberProjection

#check @SerrePositivity.KST.SConstruction.simplexFiberPostcomp
#print axioms SerrePositivity.KST.SConstruction.simplexFiberPostcomp

#check @SerrePositivity.KST.SConstruction.elementsResolution
#print axioms SerrePositivity.KST.SConstruction.elementsResolution

#check @SerrePositivity.KST.SConstruction.elementsResolutionMap
#print axioms SerrePositivity.KST.SConstruction.elementsResolutionMap

#check @SerrePositivity.KST.SConstruction.elementsResolution_obj
#print axioms SerrePositivity.KST.SConstruction.elementsResolution_obj

#check @SerrePositivity.KST.SConstruction.elementsResolutionMap_app
#print axioms SerrePositivity.KST.SConstruction.elementsResolutionMap_app

#check @SerrePositivity.KST.SConstruction.fiberResolutionCoefficient
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCoefficient

#check @SerrePositivity.KST.SConstruction.fiberResolutionCategory
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCategory

#check @SerrePositivity.KST.SConstruction.fiberResolutionValue
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionValue

#check @SerrePositivity.KST.SConstruction.fiberResolutionParameter
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionParameter

#check @SerrePositivity.KST.SConstruction.fiberResolution_condition
#print axioms SerrePositivity.KST.SConstruction.fiberResolution_condition

#check @SerrePositivity.KST.SConstruction.fiberResolutionValue_map
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionValue_map

#check @SerrePositivity.KST.SConstruction.fiberResolutionParameter_map
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionParameter_map

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonicalSimplex
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonicalSimplex

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonicalSimplex_projection
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonicalSimplex_projection

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonicalSimplex_parameter
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonicalSimplex_parameter

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonical
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonical

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonical_value
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonical_value

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonical_parameter
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonical_parameter

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonicalBaseArrow
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonicalBaseArrow

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonicalBaseArrow_map
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonicalBaseArrow_map

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonicalArrow
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonicalArrow

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonicalArrow_unique
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonicalArrow_unique

#check @SerrePositivity.KST.SConstruction.resolutionNerveMap
#print axioms SerrePositivity.KST.SConstruction.resolutionNerveMap

#check @SerrePositivity.KST.SConstruction.fiberResolutionValueFunctor
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionValueFunctor

#check @SerrePositivity.KST.SConstruction.fiberResolutionSectionFunctor
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionSectionFunctor

#check @SerrePositivity.KST.SConstruction.fiberResolutionContraction
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionContraction

#check @SerrePositivity.KST.SConstruction.fiberResolutionSectionValueIso
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionSectionValueIso

#check @SerrePositivity.KST.SConstruction.fiberResolutionValueFunctor_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionValueFunctor_localized_isIso

#check @SerrePositivity.KST.SConstruction.discreteNerveConstantIso
#print axioms SerrePositivity.KST.SConstruction.discreteNerveConstantIso

#check @SerrePositivity.KST.SConstruction.fiberResolutionRowAugmentation
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionRowAugmentation

#check @SerrePositivity.KST.SConstruction.fiberResolutionRowAugmentation_eq
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionRowAugmentation_eq

#check @SerrePositivity.KST.SConstruction.fiberResolutionRowAugmentation_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionRowAugmentation_localized_isIso

#check @SerrePositivity.KST.SConstruction.fiberResolutionRowsAugmentation
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionRowsAugmentation

#check @SerrePositivity.KST.SConstruction.constantRowsDiagonalIso
#print axioms SerrePositivity.KST.SConstruction.constantRowsDiagonalIso

#check @SerrePositivity.KST.SConstruction.fiberResolutionAugmentation
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionAugmentation

#check @SerrePositivity.KST.SConstruction.fiberResolutionAugmentation_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionAugmentation_localized_isIso

#check @SerrePositivity.KST.SConstruction.oppositeLabelledChainLift
#print axioms SerrePositivity.KST.SConstruction.oppositeLabelledChainLift

#check @SerrePositivity.KST.SConstruction.oppositeLabelledChain_reconstruct
#print axioms SerrePositivity.KST.SConstruction.oppositeLabelledChain_reconstruct

#check @SerrePositivity.KST.SConstruction.oppositeLabelledChainEquiv
#print axioms SerrePositivity.KST.SConstruction.oppositeLabelledChainEquiv

#check @SerrePositivity.KST.SConstruction.coefficientCoproduct
#print axioms SerrePositivity.KST.SConstruction.coefficientCoproduct

#check @SerrePositivity.KST.SConstruction.coefficientCoproductInclusion
#print axioms SerrePositivity.KST.SConstruction.coefficientCoproductInclusion

#check @SerrePositivity.KST.SConstruction.coefficientCoproductCofan
#print axioms SerrePositivity.KST.SConstruction.coefficientCoproductCofan

#check @SerrePositivity.KST.SConstruction.coefficientCoproductIsColimit
#print axioms SerrePositivity.KST.SConstruction.coefficientCoproductIsColimit

#check @SerrePositivity.KST.SConstruction.coefficientCoproductMap
#print axioms SerrePositivity.KST.SConstruction.coefficientCoproductMap

#check @SerrePositivity.KST.SConstruction.coefficientCoproductMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.coefficientCoproductMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.elementsResolutionRowIso
#print axioms SerrePositivity.KST.SConstruction.elementsResolutionRowIso

#check @SerrePositivity.KST.SConstruction.elementsResolutionRowIso_naturality
#print axioms SerrePositivity.KST.SConstruction.elementsResolutionRowIso_naturality

#check @SerrePositivity.KST.SConstruction.elementsResolutionRowMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.elementsResolutionRowMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.elementsResolutionMap_diagonal_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.elementsResolutionMap_diagonal_localized_isIso

#check @SerrePositivity.KST.SConstruction.constantElementsResolutionComparison
#print axioms SerrePositivity.KST.SConstruction.constantElementsResolutionComparison

#check @SerrePositivity.KST.SConstruction.constantElementsResolutionComparison_bijective
#print axioms SerrePositivity.KST.SConstruction.constantElementsResolutionComparison_bijective

#check @SerrePositivity.KST.SConstruction.constantElementsResolutionIso
#print axioms SerrePositivity.KST.SConstruction.constantElementsResolutionIso

#check @SerrePositivity.KST.SConstruction.tensorCoefficientDiagram
#print axioms SerrePositivity.KST.SConstruction.tensorCoefficientDiagram

#check @SerrePositivity.KST.SConstruction.tensorCoefficientProjection
#print axioms SerrePositivity.KST.SConstruction.tensorCoefficientProjection

#check @SerrePositivity.KST.SConstruction.tensorElementsResolutionComparison
#print axioms SerrePositivity.KST.SConstruction.tensorElementsResolutionComparison

#check @SerrePositivity.KST.SConstruction.tensorElementsResolutionEquiv
#print axioms SerrePositivity.KST.SConstruction.tensorElementsResolutionEquiv

#check @SerrePositivity.KST.SConstruction.tensorElementsResolutionComparison_eq
#print axioms SerrePositivity.KST.SConstruction.tensorElementsResolutionComparison_eq

#check @SerrePositivity.KST.SConstruction.tensorElementsResolutionIso
#print axioms SerrePositivity.KST.SConstruction.tensorElementsResolutionIso

#check @SerrePositivity.KST.SConstruction.identitySimplexFiberSection
#print axioms SerrePositivity.KST.SConstruction.identitySimplexFiberSection

#check @SerrePositivity.KST.SConstruction.identitySimplexFiberIso
#print axioms SerrePositivity.KST.SConstruction.identitySimplexFiberIso

#check @SerrePositivity.KST.SConstruction.identitySimplexFiber_toUnit_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.identitySimplexFiber_toUnit_localized_isIso

#check @SerrePositivity.KST.SConstruction.identitySimplexFiber_snd_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.identitySimplexFiber_snd_localized_isIso

#check @SerrePositivity.KST.SConstruction.simplexFiberIdentityMap
#print axioms SerrePositivity.KST.SConstruction.simplexFiberIdentityMap

#check @SerrePositivity.KST.SConstruction.simplexFiberIdentityComparison
#print axioms SerrePositivity.KST.SConstruction.simplexFiberIdentityComparison

#check @SerrePositivity.KST.SConstruction.simplexFiberProductComparison
#print axioms SerrePositivity.KST.SConstruction.simplexFiberProductComparison

#check @SerrePositivity.KST.SConstruction.simplexFiberProductComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.simplexFiberProductComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.simplexFiberResolutionProductMap
#print axioms SerrePositivity.KST.SConstruction.simplexFiberResolutionProductMap

#check @SerrePositivity.KST.SConstruction.simplexFiberResolutionProductMap_eq
#print axioms SerrePositivity.KST.SConstruction.simplexFiberResolutionProductMap_eq

#check @SerrePositivity.KST.SConstruction.simplexFiberResolutionProductMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.simplexFiberResolutionProductMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.simplicialProductQuillenA
#print axioms SerrePositivity.KST.SConstruction.simplicialProductQuillenA

#check @SerrePositivity.KST.SConstruction.objectSAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.objectSAdditivityMap

#check @SerrePositivity.KST.SConstruction.objectSAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.objectSAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.coreSRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.coreSRealizationFunctor

#check @SerrePositivity.KST.SConstruction.objectCoreRealizationComparison
#print axioms SerrePositivity.KST.SConstruction.objectCoreRealizationComparison

#check @SerrePositivity.KST.SConstruction.coreSAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.coreSAdditivityMap

#check @SerrePositivity.KST.SConstruction.objectCoreAdditivity_commute
#print axioms SerrePositivity.KST.SConstruction.objectCoreAdditivity_commute

#check @SerrePositivity.KST.SConstruction.objectCoreComparison_tensor_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.objectCoreComparison_tensor_localized_isIso

#check @SerrePositivity.KST.SConstruction.coreSAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.coreSAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.internalHomSwap_evaluate_right
#print axioms SerrePositivity.KST.SConstruction.internalHomSwap_evaluate_right

#check @SerrePositivity.KST.SConstruction.internalHomSwap_twice
#print axioms SerrePositivity.KST.SConstruction.internalHomSwap_twice

#check @SerrePositivity.KST.SConstruction.sCofiberRawTranspose
#print axioms SerrePositivity.KST.SConstruction.sCofiberRawTranspose

#check @SerrePositivity.KST.SConstruction.sCofiberRawTranspose_vertex
#print axioms SerrePositivity.KST.SConstruction.sCofiberRawTranspose_vertex

#check @SerrePositivity.KST.SConstruction.sCofiberRawTranspose_gapped
#print axioms SerrePositivity.KST.SConstruction.sCofiberRawTranspose_gapped

#check @SerrePositivity.KST.SConstruction.sCofiberTransposeSquare
#print axioms SerrePositivity.KST.SConstruction.sCofiberTransposeSquare

#check @SerrePositivity.KST.SConstruction.sCofiberTransposeSquare_ι
#print axioms SerrePositivity.KST.SConstruction.sCofiberTransposeSquare_ι

#check @SerrePositivity.KST.SConstruction.gappedVertex_isZero_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.gappedVertex_isZero_of_pointwise

#check @SerrePositivity.KST.SConstruction.gappedSquare_cofiber_iff_pointwise
#print axioms SerrePositivity.KST.SConstruction.gappedSquare_cofiber_iff_pointwise

#check @SerrePositivity.KST.SConstruction.sCofiberTransposeSquare_vertex_ι
#print axioms SerrePositivity.KST.SConstruction.sCofiberTransposeSquare_vertex_ι

#check @SerrePositivity.KST.SConstruction.sCofiberTransposeSquare_isCofiber
#print axioms SerrePositivity.KST.SConstruction.sCofiberTransposeSquare_isCofiber

#check @SerrePositivity.KST.SConstruction.sCofiberComparison
#print axioms SerrePositivity.KST.SConstruction.sCofiberComparison

#check @SerrePositivity.KST.SConstruction.sCofiberComparison_ι
#print axioms SerrePositivity.KST.SConstruction.sCofiberComparison_ι

#check @SerrePositivity.KST.SConstruction.sCofiberComparison_evaluation
#print axioms SerrePositivity.KST.SConstruction.sCofiberComparison_evaluation

#check @SerrePositivity.KST.SConstruction.isPushoutSquare_fullSubcomplex_of_ambient
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_fullSubcomplex_of_ambient

#check @SerrePositivity.KST.SConstruction.IsGapped.of_fullSubcomplex
#print axioms SerrePositivity.KST.SConstruction.IsGapped.of_fullSubcomplex

#check @SerrePositivity.KST.SConstruction.sCofiberRawInverse
#print axioms SerrePositivity.KST.SConstruction.sCofiberRawInverse

#check @SerrePositivity.KST.SConstruction.sCofiberRawInverse_vertex
#print axioms SerrePositivity.KST.SConstruction.sCofiberRawInverse_vertex

#check @SerrePositivity.KST.SConstruction.sCofiberRawInverse_cofiber
#print axioms SerrePositivity.KST.SConstruction.sCofiberRawInverse_cofiber

#check @SerrePositivity.KST.SConstruction.sCofiberInverseDiagram
#print axioms SerrePositivity.KST.SConstruction.sCofiberInverseDiagram

#check @SerrePositivity.KST.SConstruction.sCofiberInverseDiagram_ι
#print axioms SerrePositivity.KST.SConstruction.sCofiberInverseDiagram_ι

#check @SerrePositivity.KST.SConstruction.sCofiberInverseDiagram_vertex_ι
#print axioms SerrePositivity.KST.SConstruction.sCofiberInverseDiagram_vertex_ι

#check @SerrePositivity.KST.SConstruction.sCofiberInverseDiagram_isGapped
#print axioms SerrePositivity.KST.SConstruction.sCofiberInverseDiagram_isGapped

#check @SerrePositivity.KST.SConstruction.sCofiberInverse
#print axioms SerrePositivity.KST.SConstruction.sCofiberInverse

#check @SerrePositivity.KST.SConstruction.sCofiberInverse_ι
#print axioms SerrePositivity.KST.SConstruction.sCofiberInverse_ι

#check @SerrePositivity.KST.SConstruction.sCofiberComparison_double_ι
#print axioms SerrePositivity.KST.SConstruction.sCofiberComparison_double_ι

#check @SerrePositivity.KST.SConstruction.sCofiberInverse_double_ι
#print axioms SerrePositivity.KST.SConstruction.sCofiberInverse_double_ι

#check @SerrePositivity.KST.SConstruction.inverse_comp_of_commuting_mono
#print axioms SerrePositivity.KST.SConstruction.inverse_comp_of_commuting_mono

#check @SerrePositivity.KST.SConstruction.sCofiberComparison_inverse
#print axioms SerrePositivity.KST.SConstruction.sCofiberComparison_inverse

#check @SerrePositivity.KST.SConstruction.sCofiberInverse_comparison
#print axioms SerrePositivity.KST.SConstruction.sCofiberInverse_comparison

#check @SerrePositivity.KST.SConstruction.sCofiberIso
#print axioms SerrePositivity.KST.SConstruction.sCofiberIso

#check @SerrePositivity.KST.SConstruction.sCofiberStableIso
#print axioms SerrePositivity.KST.SConstruction.sCofiberStableIso

#check @SerrePositivity.KST.SConstruction.sCofiberStableIso_evaluation
#print axioms SerrePositivity.KST.SConstruction.sCofiberStableIso_evaluation

#check @SerrePositivity.KST.SConstruction.sCofiberStableIso_subobject
#print axioms SerrePositivity.KST.SConstruction.sCofiberStableIso_subobject

#check @SerrePositivity.KST.SConstruction.sCofiberStableIso_quotient
#print axioms SerrePositivity.KST.SConstruction.sCofiberStableIso_quotient

#check @SerrePositivity.KST.SConstruction.sCofiberStableIso_realization_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.sCofiberStableIso_realization_localized_isIso

#check @SerrePositivity.KST.SConstruction.sCofiberStableIso_pair
#print axioms SerrePositivity.KST.SConstruction.sCofiberStableIso_pair

#check @SerrePositivity.KST.SConstruction.coreSRowAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.coreSRowAdditivityMap

#check @SerrePositivity.KST.SConstruction.coreSRowAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.coreSRowAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.objectSRowAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.objectSRowAdditivityMap

#check @SerrePositivity.KST.SConstruction.objectSRowAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.objectSRowAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.diagonalTensorIso
#print axioms SerrePositivity.KST.SConstruction.diagonalTensorIso

#check @SerrePositivity.KST.SConstruction.diagonalTensorIso_pair
#print axioms SerrePositivity.KST.SConstruction.diagonalTensorIso_pair

#check @SerrePositivity.KST.SConstruction.coreSingleRealizationIso
#print axioms SerrePositivity.KST.SConstruction.coreSingleRealizationIso

#check @SerrePositivity.KST.SConstruction.coreSingleRealizationIso_naturality
#print axioms SerrePositivity.KST.SConstruction.coreSingleRealizationIso_naturality

#check @SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap

#check @SerrePositivity.KST.SConstruction.coreSingleRealizationIso_additivity
#print axioms SerrePositivity.KST.SConstruction.coreSingleRealizationIso_additivity

#check @SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap_one_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap_one_localized_isIso

#check @SerrePositivity.KST.SConstruction.iteratedSAdditivityDiagram
#print axioms SerrePositivity.KST.SConstruction.iteratedSAdditivityDiagram

#check @SerrePositivity.KST.SConstruction.iteratedSAdditivityDiagram_app_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.iteratedSAdditivityDiagram_app_localized_isIso

#check @SerrePositivity.KST.SConstruction.iteratedSAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.iteratedSAdditivityMap

#check @SerrePositivity.KST.SConstruction.iteratedSAdditivityMap_eq
#print axioms SerrePositivity.KST.SConstruction.iteratedSAdditivityMap_eq

#check @SerrePositivity.KST.SConstruction.iteratedSAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.iteratedSAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.iteratedSRealizationCoordinateIso_additivity
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationCoordinateIso_additivity

#check @SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap_step_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap_step_localized_isIso

#check @SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap_localized_isIso_of_pos
#print axioms SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap_localized_isIso_of_pos

#check @SerrePositivity.KST.SConstruction.ihom_map_preservesCofiberData
#print axioms SerrePositivity.KST.SConstruction.ihom_map_preservesCofiberData

#check @SerrePositivity.KST.SConstruction.cofiberPostcomp_vertex
#print axioms SerrePositivity.KST.SConstruction.cofiberPostcomp_vertex

#check @SerrePositivity.KST.SConstruction.cofiberPostcomp
#print axioms SerrePositivity.KST.SConstruction.cofiberPostcomp

#check @SerrePositivity.KST.SConstruction.cofiberPostcomp_ι
#print axioms SerrePositivity.KST.SConstruction.cofiberPostcomp_ι

#check @SerrePositivity.KST.SConstruction.cofiberPostcomp_evaluation
#print axioms SerrePositivity.KST.SConstruction.cofiberPostcomp_evaluation

#check @SerrePositivity.KST.SConstruction.preservesCofiberData_fullSubcomplex_of_comp
#print axioms SerrePositivity.KST.SConstruction.preservesCofiberData_fullSubcomplex_of_comp

#check @SerrePositivity.KST.SConstruction.cofiberPostcomp_preservesCofiberData
#print axioms SerrePositivity.KST.SConstruction.cofiberPostcomp_preservesCofiberData

#check @SerrePositivity.KST.SConstruction.cofiberPostcomp_id
#print axioms SerrePositivity.KST.SConstruction.cofiberPostcomp_id

#check @SerrePositivity.KST.SConstruction.cofiberPostcomp_comp
#print axioms SerrePositivity.KST.SConstruction.cofiberPostcomp_comp

#check @SerrePositivity.KST.SConstruction.cofiberEndofunctor
#print axioms SerrePositivity.KST.SConstruction.cofiberEndofunctor

#check @SerrePositivity.KST.SConstruction.cofiberEvaluationNat
#print axioms SerrePositivity.KST.SConstruction.cofiberEvaluationNat

#check @SerrePositivity.KST.SConstruction.cofiberSubobjectNat
#print axioms SerrePositivity.KST.SConstruction.cofiberSubobjectNat

#check @SerrePositivity.KST.SConstruction.cofiberQuotientNat
#print axioms SerrePositivity.KST.SConstruction.cofiberQuotientNat

#check @SerrePositivity.KST.SConstruction.cofiberPair_naturality
#print axioms SerrePositivity.KST.SConstruction.cofiberPair_naturality

#check @SerrePositivity.KST.SConstruction.multiRealizationAdditivityNat
#print axioms SerrePositivity.KST.SConstruction.multiRealizationAdditivityNat

#check @SerrePositivity.KST.SConstruction.multiRealizationAdditivityLocalizedIso
#print axioms SerrePositivity.KST.SConstruction.multiRealizationAdditivityLocalizedIso

#check @SerrePositivity.KST.SConstruction.multiRealizationAdditivityLocalizedIso_app
#print axioms SerrePositivity.KST.SConstruction.multiRealizationAdditivityLocalizedIso_app

#check @SerrePositivity.KST.SConstruction.sTwoCofiberComparison_evaluation
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberComparison_evaluation

#check @SerrePositivity.KST.SConstruction.sTwoRealizationAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.sTwoRealizationAdditivityMap

#check @SerrePositivity.KST.SConstruction.sTwoRealizationAdditivityMap_eq
#print axioms SerrePositivity.KST.SConstruction.sTwoRealizationAdditivityMap_eq

#check @SerrePositivity.KST.SConstruction.sTwoRealizationAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.sTwoRealizationAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.terminalBoundaryLifting_reflect_of_boundary_lifting
#print axioms SerrePositivity.KST.SConstruction.terminalBoundaryLifting_reflect_of_boundary_lifting

#check @SerrePositivity.KST.SConstruction.isLimitCone_fullSubcomplex_of_ambient
#print axioms SerrePositivity.KST.SConstruction.isLimitCone_fullSubcomplex_of_ambient

#check @SerrePositivity.KST.SConstruction.isPullbackSquare_fullSubcomplex_of_ambient
#print axioms SerrePositivity.KST.SConstruction.isPullbackSquare_fullSubcomplex_of_ambient

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate

#check @SerrePositivity.KST.SConstruction.closedSubcategory
#print axioms SerrePositivity.KST.SConstruction.closedSubcategory

#check @SerrePositivity.KST.SConstruction.closedSubcategory_quasicategory
#print axioms SerrePositivity.KST.SConstruction.closedSubcategory_quasicategory

#check @SerrePositivity.KST.SConstruction.closedSubcategory_vertex
#print axioms SerrePositivity.KST.SConstruction.closedSubcategory_vertex

#check @SerrePositivity.KST.SConstruction.square_vertices_of_corners
#print axioms SerrePositivity.KST.SConstruction.square_vertices_of_corners

#check @SerrePositivity.KST.SConstruction.fullSubcategoryVertex
#print axioms SerrePositivity.KST.SConstruction.fullSubcategoryVertex

#check @SerrePositivity.KST.SConstruction.closedSubcategory_hasZeroVertex
#print axioms SerrePositivity.KST.SConstruction.closedSubcategory_hasZeroVertex

#check @SerrePositivity.KST.SConstruction.squareBottomEdge_eq_of_pushoutSpan_eq
#print axioms SerrePositivity.KST.SConstruction.squareBottomEdge_eq_of_pushoutSpan_eq

#check @SerrePositivity.KST.SConstruction.squareLeftEdge_eq_of_pushoutSpan_eq
#print axioms SerrePositivity.KST.SConstruction.squareLeftEdge_eq_of_pushoutSpan_eq

#check @SerrePositivity.KST.SConstruction.square_initial_corners_of_span
#print axioms SerrePositivity.KST.SConstruction.square_initial_corners_of_span

#check @SerrePositivity.KST.SConstruction.exists_closedSubcategory_pushoutSquare
#print axioms SerrePositivity.KST.SConstruction.exists_closedSubcategory_pushoutSquare

#check @SerrePositivity.KST.SConstruction.closedSubcategoryInclusion_preservesPushout
#print axioms SerrePositivity.KST.SConstruction.closedSubcategoryInclusion_preservesPushout

#check @SerrePositivity.KST.SConstruction.closedSubcategoryInclusion_preservesZero
#print axioms SerrePositivity.KST.SConstruction.closedSubcategoryInclusion_preservesZero

#check @SerrePositivity.KST.SConstruction.closedSubcategoryInclusion_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.closedSubcategoryInclusion_preservesSConstructionData

#check @SerrePositivity.KST.SConstruction.exists_pullbackSquare_of_zero_corner
#print axioms SerrePositivity.KST.SConstruction.exists_pullbackSquare_of_zero_corner

#check @SerrePositivity.KST.SConstruction.square_final_corners_of_cospan
#print axioms SerrePositivity.KST.SConstruction.square_final_corners_of_cospan

#check @SerrePositivity.KST.SConstruction.exists_closedSubcategory_pullbackSquare
#print axioms SerrePositivity.KST.SConstruction.exists_closedSubcategory_pullbackSquare

#check @SerrePositivity.KST.SConstruction.closedSubcategoryInclusion_preservesFiber
#print axioms SerrePositivity.KST.SConstruction.closedSubcategoryInclusion_preservesFiber

#check @SerrePositivity.KST.SConstruction.yonedaEdge_source
#print axioms SerrePositivity.KST.SConstruction.yonedaEdge_source

#check @SerrePositivity.KST.SConstruction.yonedaEdge_target
#print axioms SerrePositivity.KST.SConstruction.yonedaEdge_target

#check @SerrePositivity.KST.SConstruction.square_bottom_vertices
#print axioms SerrePositivity.KST.SConstruction.square_bottom_vertices

#check @SerrePositivity.KST.SConstruction.square_right_vertices
#print axioms SerrePositivity.KST.SConstruction.square_right_vertices

#check @SerrePositivity.KST.SConstruction.closedSubcategory_cofiber_nonempty
#print axioms SerrePositivity.KST.SConstruction.closedSubcategory_cofiber_nonempty

#check @SerrePositivity.KST.SConstruction.closedSubcategory_fiber_nonempty
#print axioms SerrePositivity.KST.SConstruction.closedSubcategory_fiber_nonempty

#check @SerrePositivity.KST.SConstruction.closedSubcategory_isStable
#print axioms SerrePositivity.KST.SConstruction.closedSubcategory_isStable

#check @SerrePositivity.KST.SConstruction.closedStableModel
#print axioms SerrePositivity.KST.SConstruction.closedStableModel

#check @SerrePositivity.KST.SConstruction.closedStableInclusion
#print axioms SerrePositivity.KST.SConstruction.closedStableInclusion

#check @SerrePositivity.KST.SConstruction.PreservesCofiberData.isExactFunctor
#print axioms SerrePositivity.KST.SConstruction.PreservesCofiberData.isExactFunctor

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.comap
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.comap

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.inter
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.inter

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.top
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.top

#check @SerrePositivity.KST.SConstruction.relativeCofiberPredicate
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberPredicate

#check @SerrePositivity.KST.SConstruction.relativeCofiberDiagrams
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberDiagrams

#check @SerrePositivity.KST.SConstruction.relativeCofiberDiagrams_quasicategory
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberDiagrams_quasicategory

#check @SerrePositivity.KST.SConstruction.relativeCofiberDiagrams_isStable
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberDiagrams_isStable

#check @SerrePositivity.KST.SConstruction.relativeCofiberStableModel
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberStableModel

#check @SerrePositivity.KST.SConstruction.relativeCofiberInclusion
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberInclusion

#check @SerrePositivity.KST.SConstruction.relativeCofiber_vertex
#print axioms SerrePositivity.KST.SConstruction.relativeCofiber_vertex

#check @SerrePositivity.KST.SConstruction.relativeCofiberSubobjectMap
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberSubobjectMap

#check @SerrePositivity.KST.SConstruction.relativeCofiberQuotientMap
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberQuotientMap

#check @SerrePositivity.KST.SConstruction.relativeCofiberSubobjectMap_ι
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberSubobjectMap_ι

#check @SerrePositivity.KST.SConstruction.relativeCofiberQuotientMap_ι
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberQuotientMap_ι

#check @SerrePositivity.KST.SConstruction.relativeCofiberSubobject
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberSubobject

#check @SerrePositivity.KST.SConstruction.relativeCofiberQuotient
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberQuotient

#check @SerrePositivity.KST.SConstruction.relativeCofiberSubobject_inclusion
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberSubobject_inclusion

#check @SerrePositivity.KST.SConstruction.relativeCofiberQuotient_inclusion
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberQuotient_inclusion

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.predicate
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.predicate

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.of_iso
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.of_iso

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.zero_mem
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.zero_mem

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.pushout_mem
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.pushout_mem

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.pullback_mem
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.pullback_mem

#check @SerrePositivity.KST.SConstruction.objectSConstructionFunctor_map_injective
#print axioms SerrePositivity.KST.SConstruction.objectSConstructionFunctor_map_injective

#check @SerrePositivity.KST.SConstruction.objectSConstructionFunctor_map_mono
#print axioms SerrePositivity.KST.SConstruction.objectSConstructionFunctor_map_mono

#check @SerrePositivity.KST.SConstruction.ObjectSInClosed
#print axioms SerrePositivity.KST.SConstruction.ObjectSInClosed

#check @SerrePositivity.KST.SConstruction.objectSClosedInclusion_mem
#print axioms SerrePositivity.KST.SConstruction.objectSClosedInclusion_mem

#check @SerrePositivity.KST.SConstruction.objectSClosedVertexLift
#print axioms SerrePositivity.KST.SConstruction.objectSClosedVertexLift

#check @SerrePositivity.KST.SConstruction.objectSClosedVertexLift_diagram
#print axioms SerrePositivity.KST.SConstruction.objectSClosedVertexLift_diagram

#check @SerrePositivity.KST.SConstruction.objectSClosedVertexLift_inclusion
#print axioms SerrePositivity.KST.SConstruction.objectSClosedVertexLift_inclusion

#check @SerrePositivity.KST.SConstruction.ObjectSInClosed.map
#print axioms SerrePositivity.KST.SConstruction.ObjectSInClosed.map

#check @SerrePositivity.KST.SConstruction.closedObjectSSubcomplex
#print axioms SerrePositivity.KST.SConstruction.closedObjectSSubcomplex

#check @SerrePositivity.KST.SConstruction.closedObjectSConstruction
#print axioms SerrePositivity.KST.SConstruction.closedObjectSConstruction

#check @SerrePositivity.KST.SConstruction.closedObjectSInclusion
#print axioms SerrePositivity.KST.SConstruction.closedObjectSInclusion

#check @SerrePositivity.KST.SConstruction.objectSClosedForward
#print axioms SerrePositivity.KST.SConstruction.objectSClosedForward

#check @SerrePositivity.KST.SConstruction.objectSClosedBackward
#print axioms SerrePositivity.KST.SConstruction.objectSClosedBackward

#check @SerrePositivity.KST.SConstruction.objectSClosedIso
#print axioms SerrePositivity.KST.SConstruction.objectSClosedIso

#check @SerrePositivity.KST.SConstruction.objectSClosedForward_inclusion
#print axioms SerrePositivity.KST.SConstruction.objectSClosedForward_inclusion

#check @SerrePositivity.KST.SConstruction.closedObjectSFamily
#print axioms SerrePositivity.KST.SConstruction.closedObjectSFamily

#check @SerrePositivity.KST.SConstruction.objectSClosedBackward_inclusion
#print axioms SerrePositivity.KST.SConstruction.objectSClosedBackward_inclusion

#check @SerrePositivity.KST.SConstruction.objectSClosedFamilyLift
#print axioms SerrePositivity.KST.SConstruction.objectSClosedFamilyLift

#check @SerrePositivity.KST.SConstruction.objectSClosedFamilyLift_inclusion
#print axioms SerrePositivity.KST.SConstruction.objectSClosedFamilyLift_inclusion

#check @SerrePositivity.KST.SConstruction.objectSClosedFamilyLift_unique
#print axioms SerrePositivity.KST.SConstruction.objectSClosedFamilyLift_unique

#check @SerrePositivity.KST.SConstruction.relativeCofiberObjectSubobject_square
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberObjectSubobject_square

#check @SerrePositivity.KST.SConstruction.relativeCofiberObjectQuotient_square
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberObjectQuotient_square

#check @SerrePositivity.KST.SConstruction.relativeCofiberSubobjectLeftFiber
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberSubobjectLeftFiber

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberQuotient
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberQuotient

#check @SerrePositivity.KST.SConstruction.relativeCofiberBaseSimplex
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberBaseSimplex

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_projection
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_projection

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_parameter
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_parameter

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_quotient
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_quotient

#check @SerrePositivity.KST.SConstruction.objectSInRelativeCofiber_iff
#print axioms SerrePositivity.KST.SConstruction.objectSInRelativeCofiber_iff

#check @SerrePositivity.KST.SConstruction.cofiberLeftFiberSubobject_in_closed
#print axioms SerrePositivity.KST.SConstruction.cofiberLeftFiberSubobject_in_closed

#check @SerrePositivity.KST.SConstruction.cofiberLeftFiber_in_relative_iff
#print axioms SerrePositivity.KST.SConstruction.cofiberLeftFiber_in_relative_iff

#check @SerrePositivity.KST.SConstruction.relativeCofiberBaseSimplex_in_closed
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberBaseSimplex_in_closed

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_quotient_in_closed
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_quotient_in_closed

#check @SerrePositivity.KST.SConstruction.relativeCofiberFiberObjectLift
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberFiberObjectLift

#check @SerrePositivity.KST.SConstruction.relativeCofiberFiberObjectLift_inclusion
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberFiberObjectLift_inclusion

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberLift
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberLift

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberLift_forget
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberLift_forget

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_mono
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_mono

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyRho_quotient_in_closed
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyRho_quotient_in_closed

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyRhoFiberMap
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyRhoFiberMap

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyRhoFiberMap_forget
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyRhoFiberMap_forget

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyRhoFiberMap_zero
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyRhoFiberMap_zero

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyRhoFiberMap_quotient
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyRhoFiberMap_quotient

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyRhoTerminal
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyRhoTerminal

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyRhoHomotopy
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyRhoHomotopy

#check @SerrePositivity.KST.SConstruction.relativeMcCarthySection_quotient_in_closed
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthySection_quotient_in_closed

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyFiberSection
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyFiberSection

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyFiberSection_forget
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyFiberSection_forget

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyFiberSection_quotient
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyFiberSection_quotient

#check @SerrePositivity.KST.SConstruction.ObjectSInClosed.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.ObjectSInClosed.of_functorIso

#check @SerrePositivity.KST.SConstruction.mcCarthyThetaObject_quotient_in_closed
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaObject_quotient_in_closed

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyTheta_quotient_in_closed
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyTheta_quotient_in_closed

#check @SerrePositivity.KST.SConstruction.tensorIntervalEndpoint_naturality
#print axioms SerrePositivity.KST.SConstruction.tensorIntervalEndpoint_naturality

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyRhoTerminal_forget
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyRhoTerminal_forget

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyThetaFiberMap
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyThetaFiberMap

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyThetaFiberMap_forget
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyThetaFiberMap_forget

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyThetaFiberMap_zero
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyThetaFiberMap_zero

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyThetaFiberMap_one
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyThetaFiberMap_one

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyThetaHomotopy
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyThetaHomotopy

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyFiber_retraction_localized
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyFiber_retraction_localized

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberQuotient_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberQuotient_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeObjectSAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.relativeObjectSAdditivityMap

#check @SerrePositivity.KST.SConstruction.relativeObjectSAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeObjectSAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.objectCoreComparisons_tensor_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.objectCoreComparisons_tensor_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeCoreSAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.relativeCoreSAdditivityMap

#check @SerrePositivity.KST.SConstruction.relativeObjectCoreAdditivity_commute
#print axioms SerrePositivity.KST.SConstruction.relativeObjectCoreAdditivity_commute

#check @SerrePositivity.KST.SConstruction.relativeCoreSAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeCoreSAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.iInter
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.iInter

#check @SerrePositivity.KST.SConstruction.sStableEvaluation
#print axioms SerrePositivity.KST.SConstruction.sStableEvaluation

#check @SerrePositivity.KST.SConstruction.sClosedPredicate
#print axioms SerrePositivity.KST.SConstruction.sClosedPredicate

#check @SerrePositivity.KST.SConstruction.sClosedPredicate_iff
#print axioms SerrePositivity.KST.SConstruction.sClosedPredicate_iff

#check @SerrePositivity.KST.SConstruction.diagramVertex_postcomp
#print axioms SerrePositivity.KST.SConstruction.diagramVertex_postcomp

#check @SerrePositivity.KST.SConstruction.sClosedDiagramLift
#print axioms SerrePositivity.KST.SConstruction.sClosedDiagramLift

#check @SerrePositivity.KST.SConstruction.sClosedDiagramLift_ι
#print axioms SerrePositivity.KST.SConstruction.sClosedDiagramLift_ι

#check @SerrePositivity.KST.SConstruction.sClosedDiagramLift_vertex_ι
#print axioms SerrePositivity.KST.SConstruction.sClosedDiagramLift_vertex_ι

#check @SerrePositivity.KST.SConstruction.sClosedFamilyLift
#print axioms SerrePositivity.KST.SConstruction.sClosedFamilyLift

#check @SerrePositivity.KST.SConstruction.sClosedFamilyLift_inclusion
#print axioms SerrePositivity.KST.SConstruction.sClosedFamilyLift_inclusion

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_mono
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_mono

#check @SerrePositivity.KST.SConstruction.sClosedInclusion_vertex
#print axioms SerrePositivity.KST.SConstruction.sClosedInclusion_vertex

#check @SerrePositivity.KST.SConstruction.sClosedComparison
#print axioms SerrePositivity.KST.SConstruction.sClosedComparison

#check @SerrePositivity.KST.SConstruction.sClosedComparison_inclusion
#print axioms SerrePositivity.KST.SConstruction.sClosedComparison_inclusion

#check @SerrePositivity.KST.SConstruction.sClosedInverse
#print axioms SerrePositivity.KST.SConstruction.sClosedInverse

#check @SerrePositivity.KST.SConstruction.sClosedInverse_inclusion
#print axioms SerrePositivity.KST.SConstruction.sClosedInverse_inclusion

#check @SerrePositivity.KST.SConstruction.sClosedIso
#print axioms SerrePositivity.KST.SConstruction.sClosedIso

#check @SerrePositivity.KST.SConstruction.sClosedStableIso
#print axioms SerrePositivity.KST.SConstruction.sClosedStableIso

#check @SerrePositivity.KST.SConstruction.sClosedStableIso_inclusion
#print axioms SerrePositivity.KST.SConstruction.sClosedStableIso_inclusion

#check @SerrePositivity.KST.SConstruction.sStableEvaluation_naturality
#print axioms SerrePositivity.KST.SConstruction.sStableEvaluation_naturality

#check @SerrePositivity.KST.SConstruction.closedStableInclusion_cancel
#print axioms SerrePositivity.KST.SConstruction.closedStableInclusion_cancel

#check @SerrePositivity.KST.SConstruction.sCofiberStableIso_subobject_component
#print axioms SerrePositivity.KST.SConstruction.sCofiberStableIso_subobject_component

#check @SerrePositivity.KST.SConstruction.sCofiberStableIso_quotient_component
#print axioms SerrePositivity.KST.SConstruction.sCofiberStableIso_quotient_component

#check @SerrePositivity.KST.SConstruction.sCofiber_relativePredicate_iff
#print axioms SerrePositivity.KST.SConstruction.sCofiber_relativePredicate_iff

#check @SerrePositivity.KST.SConstruction.sRelativeRestrictionIso
#print axioms SerrePositivity.KST.SConstruction.sRelativeRestrictionIso

#check @SerrePositivity.KST.SConstruction.sRelativeRestrictionIso_inclusion
#print axioms SerrePositivity.KST.SConstruction.sRelativeRestrictionIso_inclusion

#check @SerrePositivity.KST.SConstruction.sRelativeCofiberIso
#print axioms SerrePositivity.KST.SConstruction.sRelativeCofiberIso

#check @SerrePositivity.KST.SConstruction.sRelativeCofiberIso_inclusion
#print axioms SerrePositivity.KST.SConstruction.sRelativeCofiberIso_inclusion

#check @SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso
#print axioms SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso

#check @SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso_inclusion
#print axioms SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso_inclusion

#check @SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso_subobject
#print axioms SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso_subobject

#check @SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso_quotient
#print axioms SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso_quotient

#check @SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso_pair
#print axioms SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso_pair

#check @SerrePositivity.KST.SConstruction.relativeRowAdditivity_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeRowAdditivity_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeCoreSRowAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.relativeCoreSRowAdditivityMap

#check @SerrePositivity.KST.SConstruction.relativeCoreSRowAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeCoreSRowAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeObjectSRowAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.relativeObjectSRowAdditivityMap

#check @SerrePositivity.KST.SConstruction.relativeObjectSRowAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeObjectSRowAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap

#check @SerrePositivity.KST.SConstruction.coreSingleRealizationIso_relativeAdditivity
#print axioms SerrePositivity.KST.SConstruction.coreSingleRealizationIso_relativeAdditivity

#check @SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap_one_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap_one_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityDiagram
#print axioms SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityDiagram

#check @SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityDiagram_app_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityDiagram_app_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityMap

#check @SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityMap_eq
#print axioms SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityMap_eq

#check @SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.iteratedSRealizationCoordinateIso_relativeAdditivity
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationCoordinateIso_relativeAdditivity

#check @SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap_step_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap_step_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap_localized_isIso_of_pos
#print axioms SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap_localized_isIso_of_pos

#check @SerrePositivity.KST.SConstruction.closedSubcategoryMap
#print axioms SerrePositivity.KST.SConstruction.closedSubcategoryMap

#check @SerrePositivity.KST.SConstruction.closedSubcategoryMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.closedSubcategoryMap_inclusion

#check @SerrePositivity.KST.SConstruction.closedStableMap
#print axioms SerrePositivity.KST.SConstruction.closedStableMap

#check @SerrePositivity.KST.SConstruction.closedStableMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.closedStableMap_inclusion

#check @SerrePositivity.KST.SConstruction.closedStableMap_id
#print axioms SerrePositivity.KST.SConstruction.closedStableMap_id

#check @SerrePositivity.KST.SConstruction.closedStableMap_comp
#print axioms SerrePositivity.KST.SConstruction.closedStableMap_comp

#check @SerrePositivity.KST.SConstruction.RelativeStableModel
#print axioms SerrePositivity.KST.SConstruction.RelativeStableModel

#check @SerrePositivity.KST.SConstruction.relativeStableModelCategory
#print axioms SerrePositivity.KST.SConstruction.relativeStableModelCategory

#check @SerrePositivity.KST.SConstruction.relativeAmbientFunctor
#print axioms SerrePositivity.KST.SConstruction.relativeAmbientFunctor

#check @SerrePositivity.KST.SConstruction.relativeLeftFunctor
#print axioms SerrePositivity.KST.SConstruction.relativeLeftFunctor

#check @SerrePositivity.KST.SConstruction.relativeRightFunctor
#print axioms SerrePositivity.KST.SConstruction.relativeRightFunctor

#check @SerrePositivity.KST.SConstruction.relativeCofiberPostcomp_mem
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberPostcomp_mem

#check @SerrePositivity.KST.SConstruction.relativeCofiberMap
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberMap

#check @SerrePositivity.KST.SConstruction.relativeCofiberMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberMap_inclusion

#check @SerrePositivity.KST.SConstruction.relativeCofiberFunctor
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberFunctor

#check @SerrePositivity.KST.SConstruction.relativeCofiberInclusionNat
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberInclusionNat

#check @SerrePositivity.KST.SConstruction.relativeCofiberSubobject_naturality
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberSubobject_naturality

#check @SerrePositivity.KST.SConstruction.relativeCofiberSubobjectNat
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberSubobjectNat

#check @SerrePositivity.KST.SConstruction.relativeCofiberQuotient_naturality
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberQuotient_naturality

#check @SerrePositivity.KST.SConstruction.relativeCofiberQuotientNat
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberQuotientNat

#check @SerrePositivity.KST.SConstruction.relativeCofiberPair_naturality
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberPair_naturality

#check @SerrePositivity.KST.SConstruction.relativeAdditivityNat
#print axioms SerrePositivity.KST.SConstruction.relativeAdditivityNat

#check @SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityNat
#print axioms SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityNat

#check @SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityLocalizedIso
#print axioms SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityLocalizedIso

#check @SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityLocalizedIso_app
#print axioms SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityLocalizedIso_app

#check @SerrePositivity.KST.SConstruction.RelativeStableModel.ambient
#print axioms SerrePositivity.KST.SConstruction.RelativeStableModel.ambient

#check @SerrePositivity.KST.SConstruction.RelativeStableModel.left
#print axioms SerrePositivity.KST.SConstruction.RelativeStableModel.left

#check @SerrePositivity.KST.SConstruction.RelativeStableModel.right
#print axioms SerrePositivity.KST.SConstruction.RelativeStableModel.right

#check @SerrePositivity.KST.SConstruction.cutEndpoint
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint

#check @SerrePositivity.KST.SConstruction.cutEndpoint_mono
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint_mono

#check @SerrePositivity.KST.SConstruction.cutEndpoint_zero_zero
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint_zero_zero

#check @SerrePositivity.KST.SConstruction.cutEndpoint_one_zero
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint_one_zero

#check @SerrePositivity.KST.SConstruction.cutEndpoint_zero_one
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint_zero_one

#check @SerrePositivity.KST.SConstruction.cutEndpoint_one_one
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint_one_one

#check @SerrePositivity.KST.SConstruction.arCutSquareOrder
#print axioms SerrePositivity.KST.SConstruction.arCutSquareOrder

#check @SerrePositivity.KST.SConstruction.arCutSquareChain
#print axioms SerrePositivity.KST.SConstruction.arCutSquareChain

#check @SerrePositivity.KST.SConstruction.arCutSquareMap
#print axioms SerrePositivity.KST.SConstruction.arCutSquareMap

#check @SerrePositivity.KST.SConstruction.arCutSquareAt
#print axioms SerrePositivity.KST.SConstruction.arCutSquareAt

#check @SerrePositivity.KST.SConstruction.cutEndpoint_of_le
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint_of_le

#check @SerrePositivity.KST.SConstruction.cutEndpoint_of_ge
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint_of_ge

#check @SerrePositivity.KST.SConstruction.arIntervalOrder
#print axioms SerrePositivity.KST.SConstruction.arIntervalOrder

#check @SerrePositivity.KST.SConstruction.arIntervalEdge
#print axioms SerrePositivity.KST.SConstruction.arIntervalEdge

#check @SerrePositivity.KST.SConstruction.arCutSquareAt_crossing
#print axioms SerrePositivity.KST.SConstruction.arCutSquareAt_crossing

#check @SerrePositivity.KST.SConstruction.arCutSquareAt_left
#print axioms SerrePositivity.KST.SConstruction.arCutSquareAt_left

#check @SerrePositivity.KST.SConstruction.arCutSquareAt_right
#print axioms SerrePositivity.KST.SConstruction.arCutSquareAt_right

#check @SerrePositivity.KST.SConstruction.arCutSquareAt_zero_corner
#print axioms SerrePositivity.KST.SConstruction.arCutSquareAt_zero_corner

#check @SerrePositivity.KST.SConstruction.arCutSquareAt_isPushout
#print axioms SerrePositivity.KST.SConstruction.arCutSquareAt_isPushout

#check @SerrePositivity.KST.SConstruction.arCutSquareAt_isCofiber
#print axioms SerrePositivity.KST.SConstruction.arCutSquareAt_isCofiber

#check @SerrePositivity.KST.SConstruction.arCutFamily
#print axioms SerrePositivity.KST.SConstruction.arCutFamily

#check @SerrePositivity.KST.SConstruction.arCutFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.arCutFamily_vertex

#check @SerrePositivity.KST.SConstruction.gappedCutCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.gappedCutCofiberFamily

#check @SerrePositivity.KST.SConstruction.gappedCutCofiberFamily_ι
#print axioms SerrePositivity.KST.SConstruction.gappedCutCofiberFamily_ι

#check @SerrePositivity.KST.SConstruction.cutCornerOrder
#print axioms SerrePositivity.KST.SConstruction.cutCornerOrder

#check @SerrePositivity.KST.SConstruction.arCutSquareMap_corner
#print axioms SerrePositivity.KST.SConstruction.arCutSquareMap_corner

#check @SerrePositivity.KST.SConstruction.arCutFamily_evaluation
#print axioms SerrePositivity.KST.SConstruction.arCutFamily_evaluation

#check @SerrePositivity.KST.SConstruction.gappedCutCofiberFamily_evaluation
#print axioms SerrePositivity.KST.SConstruction.gappedCutCofiberFamily_evaluation

#check @SerrePositivity.KST.SConstruction.gappedCutCofiberFamily_isGapped
#print axioms SerrePositivity.KST.SConstruction.gappedCutCofiberFamily_isGapped

#check @SerrePositivity.KST.SConstruction.cutDiagramFamilyOperator
#print axioms SerrePositivity.KST.SConstruction.cutDiagramFamilyOperator

#check @SerrePositivity.KST.SConstruction.cutRawFamilyOperator
#print axioms SerrePositivity.KST.SConstruction.cutRawFamilyOperator

#check @SerrePositivity.KST.SConstruction.cutRawFamilyOperator_vertex
#print axioms SerrePositivity.KST.SConstruction.cutRawFamilyOperator_vertex

#check @SerrePositivity.KST.SConstruction.cutRawFamilyOperator_isCofiber
#print axioms SerrePositivity.KST.SConstruction.cutRawFamilyOperator_isCofiber

#check @SerrePositivity.KST.SConstruction.cutCofiberFamilyOperator
#print axioms SerrePositivity.KST.SConstruction.cutCofiberFamilyOperator

#check @SerrePositivity.KST.SConstruction.cutCofiberFamilyOperator_ι
#print axioms SerrePositivity.KST.SConstruction.cutCofiberFamilyOperator_ι

#check @SerrePositivity.KST.SConstruction.cutCofiberFamilyOperator_vertex_ι
#print axioms SerrePositivity.KST.SConstruction.cutCofiberFamilyOperator_vertex_ι

#check @SerrePositivity.KST.SConstruction.cutCofiberFamilyOperator_isGapped
#print axioms SerrePositivity.KST.SConstruction.cutCofiberFamilyOperator_isGapped

#check @SerrePositivity.KST.SConstruction.cutSConstructionMap
#print axioms SerrePositivity.KST.SConstruction.cutSConstructionMap

#check @SerrePositivity.KST.SConstruction.cutSConstructionMap_ι
#print axioms SerrePositivity.KST.SConstruction.cutSConstructionMap_ι

#check @SerrePositivity.KST.SConstruction.cutCofiberComparison
#print axioms SerrePositivity.KST.SConstruction.cutCofiberComparison

#check @SerrePositivity.KST.SConstruction.cutDiagramFamilyOperator_evaluation
#print axioms SerrePositivity.KST.SConstruction.cutDiagramFamilyOperator_evaluation

#check @SerrePositivity.KST.SConstruction.cutRawFamilyOperator_evaluation
#print axioms SerrePositivity.KST.SConstruction.cutRawFamilyOperator_evaluation

#check @SerrePositivity.KST.SConstruction.cutSConstructionMap_evaluation
#print axioms SerrePositivity.KST.SConstruction.cutSConstructionMap_evaluation

#check @SerrePositivity.KST.SConstruction.cutCofiberComparison_evaluation
#print axioms SerrePositivity.KST.SConstruction.cutCofiberComparison_evaluation

#check @SerrePositivity.KST.SConstruction.cutCofiberComparison_preservesCofiberData
#print axioms SerrePositivity.KST.SConstruction.cutCofiberComparison_preservesCofiberData

#check @SerrePositivity.KST.SConstruction.cutStableComparison
#print axioms SerrePositivity.KST.SConstruction.cutStableComparison

#check @SerrePositivity.KST.SConstruction.cutStableComparison_evaluation
#print axioms SerrePositivity.KST.SConstruction.cutStableComparison_evaluation

#check @SerrePositivity.KST.SConstruction.cutCornerOrder_one_zero
#print axioms SerrePositivity.KST.SConstruction.cutCornerOrder_one_zero

#check @SerrePositivity.KST.SConstruction.cutStableComparison_middle
#print axioms SerrePositivity.KST.SConstruction.cutStableComparison_middle

#check @SerrePositivity.KST.SConstruction.cutEndpoint_naturality
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint_naturality

#check @SerrePositivity.KST.SConstruction.cutCornerOrder_naturality
#print axioms SerrePositivity.KST.SConstruction.cutCornerOrder_naturality

#check @SerrePositivity.KST.SConstruction.arCutSquareMap_naturality
#print axioms SerrePositivity.KST.SConstruction.arCutSquareMap_naturality

#check @SerrePositivity.KST.SConstruction.zeroStablePredicate
#print axioms SerrePositivity.KST.SConstruction.zeroStablePredicate

#check @SerrePositivity.KST.SConstruction.cutLeftSupport
#print axioms SerrePositivity.KST.SConstruction.cutLeftSupport

#check @SerrePositivity.KST.SConstruction.cutRightSupport
#print axioms SerrePositivity.KST.SConstruction.cutRightSupport

#check @SerrePositivity.KST.SConstruction.cutLeftSupport_iff
#print axioms SerrePositivity.KST.SConstruction.cutLeftSupport_iff

#check @SerrePositivity.KST.SConstruction.cutRightSupport_iff
#print axioms SerrePositivity.KST.SConstruction.cutRightSupport_iff

#check @SerrePositivity.KST.SConstruction.sConstructionVertex_diagonal_isZero
#print axioms SerrePositivity.KST.SConstruction.sConstructionVertex_diagonal_isZero

#check @SerrePositivity.KST.SConstruction.sMap_evaluate_vertex
#print axioms SerrePositivity.KST.SConstruction.sMap_evaluate_vertex

#check @SerrePositivity.KST.SConstruction.cutLeftSupport_sMap
#print axioms SerrePositivity.KST.SConstruction.cutLeftSupport_sMap

#check @SerrePositivity.KST.SConstruction.cutRightSupport_sMap
#print axioms SerrePositivity.KST.SConstruction.cutRightSupport_sMap

#check @SerrePositivity.KST.SConstruction.cutStableComparison_relative_mem
#print axioms SerrePositivity.KST.SConstruction.cutStableComparison_relative_mem

#check @SerrePositivity.KST.SConstruction.cutRelativeComparisonMap
#print axioms SerrePositivity.KST.SConstruction.cutRelativeComparisonMap

#check @SerrePositivity.KST.SConstruction.cutRelativeComparisonMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.cutRelativeComparisonMap_inclusion

#check @SerrePositivity.KST.SConstruction.cutRelativeComparison
#print axioms SerrePositivity.KST.SConstruction.cutRelativeComparison

#check @SerrePositivity.KST.SConstruction.cutRelativeComparison_inclusion
#print axioms SerrePositivity.KST.SConstruction.cutRelativeComparison_inclusion

#check @SerrePositivity.KST.SConstruction.cutRelativeMiddle
#print axioms SerrePositivity.KST.SConstruction.cutRelativeMiddle

#check @SerrePositivity.KST.SConstruction.cutRelativeComparison_middle
#print axioms SerrePositivity.KST.SConstruction.cutRelativeComparison_middle

#check @SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_corner
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_corner

#check @SerrePositivity.KST.SConstruction.cofiberFamilyBottomIso
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyBottomIso

#check @SerrePositivity.KST.SConstruction.cofiberFamilyRightIso
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyRightIso

#check @SerrePositivity.KST.SConstruction.cutLeftSupport_rightCut_isZero
#print axioms SerrePositivity.KST.SConstruction.cutLeftSupport_rightCut_isZero

#check @SerrePositivity.KST.SConstruction.cutRightSupport_leftCut_isZero
#print axioms SerrePositivity.KST.SConstruction.cutRightSupport_leftCut_isZero

#check @SerrePositivity.KST.SConstruction.cutComparison_pre_evaluation
#print axioms SerrePositivity.KST.SConstruction.cutComparison_pre_evaluation

#check @SerrePositivity.KST.SConstruction.cutComparison_pre_middle
#print axioms SerrePositivity.KST.SConstruction.cutComparison_pre_middle

#check @SerrePositivity.KST.SConstruction.cutLeftSupport_normalizationIso
#print axioms SerrePositivity.KST.SConstruction.cutLeftSupport_normalizationIso

#check @SerrePositivity.KST.SConstruction.cutRightSupport_normalizationIso
#print axioms SerrePositivity.KST.SConstruction.cutRightSupport_normalizationIso

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalInclusion
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalInclusion

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalRetraction
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalRetraction

#check @SerrePositivity.KST.SConstruction.cutRightIntervalInclusion
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalInclusion

#check @SerrePositivity.KST.SConstruction.cutRightIntervalRetraction
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalRetraction

#check @SerrePositivity.KST.SConstruction.cutLeftInterval_retraction_inclusion
#print axioms SerrePositivity.KST.SConstruction.cutLeftInterval_retraction_inclusion

#check @SerrePositivity.KST.SConstruction.cutLeftInterval_inclusion_retraction
#print axioms SerrePositivity.KST.SConstruction.cutLeftInterval_inclusion_retraction

#check @SerrePositivity.KST.SConstruction.cutRightInterval_retraction_inclusion
#print axioms SerrePositivity.KST.SConstruction.cutRightInterval_retraction_inclusion

#check @SerrePositivity.KST.SConstruction.cutRightInterval_inclusion_retraction
#print axioms SerrePositivity.KST.SConstruction.cutRightInterval_inclusion_retraction

#check @SerrePositivity.KST.SConstruction.functorIsoOfFullSubcomplexPostcomp
#print axioms SerrePositivity.KST.SConstruction.functorIsoOfFullSubcomplexPostcomp

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalExtension_mem
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalExtension_mem

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalExtensionMap
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalExtensionMap

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalExtensionMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalExtensionMap_inclusion

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalExtension
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalExtension

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalRestriction
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalRestriction

#check @SerrePositivity.KST.SConstruction.cutRightIntervalExtension_mem
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalExtension_mem

#check @SerrePositivity.KST.SConstruction.cutRightIntervalExtensionMap
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalExtensionMap

#check @SerrePositivity.KST.SConstruction.cutRightIntervalExtensionMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalExtensionMap_inclusion

#check @SerrePositivity.KST.SConstruction.cutRightIntervalExtension
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalExtension

#check @SerrePositivity.KST.SConstruction.cutRightIntervalRestriction
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalRestriction

#check @SerrePositivity.KST.SConstruction.cutLeftInterval_extension_restriction
#print axioms SerrePositivity.KST.SConstruction.cutLeftInterval_extension_restriction

#check @SerrePositivity.KST.SConstruction.cutLeftInterval_restriction_extension_inclusion
#print axioms SerrePositivity.KST.SConstruction.cutLeftInterval_restriction_extension_inclusion

#check @SerrePositivity.KST.SConstruction.cutLeftInterval_restriction_extensionIso
#print axioms SerrePositivity.KST.SConstruction.cutLeftInterval_restriction_extensionIso

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalEquivalence
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalEquivalence

#check @SerrePositivity.KST.SConstruction.cutRightInterval_extension_restriction
#print axioms SerrePositivity.KST.SConstruction.cutRightInterval_extension_restriction

#check @SerrePositivity.KST.SConstruction.cutRightInterval_restriction_extension_inclusion
#print axioms SerrePositivity.KST.SConstruction.cutRightInterval_restriction_extension_inclusion

#check @SerrePositivity.KST.SConstruction.cutRightInterval_restriction_extensionIso
#print axioms SerrePositivity.KST.SConstruction.cutRightInterval_restriction_extensionIso

#check @SerrePositivity.KST.SConstruction.cutRightIntervalEquivalence
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalEquivalence

#check @SerrePositivity.KST.SConstruction.arrowSquareDiagonal
#print axioms SerrePositivity.KST.SConstruction.arrowSquareDiagonal

#check @SerrePositivity.KST.SConstruction.arrowTrianglePrism
#print axioms SerrePositivity.KST.SConstruction.arrowTrianglePrism

#check @SerrePositivity.KST.SConstruction.arrowTrianglePrism_zero
#print axioms SerrePositivity.KST.SConstruction.arrowTrianglePrism_zero

#check @SerrePositivity.KST.SConstruction.arrowTrianglePrism_one
#print axioms SerrePositivity.KST.SConstruction.arrowTrianglePrism_one

#check @SerrePositivity.KST.SConstruction.arrowTrianglePrism_source
#print axioms SerrePositivity.KST.SConstruction.arrowTrianglePrism_source

#check @SerrePositivity.KST.SConstruction.arrowTrianglePrism_target
#print axioms SerrePositivity.KST.SConstruction.arrowTrianglePrism_target

#check @SerrePositivity.KST.SConstruction.arrowTrianglePrismIso
#print axioms SerrePositivity.KST.SConstruction.arrowTrianglePrismIso

#check @SerrePositivity.KST.SConstruction.arrowSquareTopRightIso
#print axioms SerrePositivity.KST.SConstruction.arrowSquareTopRightIso

#check @SerrePositivity.KST.SConstruction.evaluateFunctorAt_as_ev
#print axioms SerrePositivity.KST.SConstruction.evaluateFunctorAt_as_ev

#check @SerrePositivity.KST.SConstruction.ihomUncurry_pre_row
#print axioms SerrePositivity.KST.SConstruction.ihomUncurry_pre_row

#check @SerrePositivity.KST.SConstruction.ihomUncurry_pre_column
#print axioms SerrePositivity.KST.SConstruction.ihomUncurry_pre_column

#check @SerrePositivity.KST.SConstruction.cofiberBottomEvaluationMap
#print axioms SerrePositivity.KST.SConstruction.cofiberBottomEvaluationMap

#check @SerrePositivity.KST.SConstruction.cofiberProjection_evaluation
#print axioms SerrePositivity.KST.SConstruction.cofiberProjection_evaluation

#check @SerrePositivity.KST.SConstruction.cofiberPostcomp_projection
#print axioms SerrePositivity.KST.SConstruction.cofiberPostcomp_projection

#check @SerrePositivity.KST.SConstruction.doubleCofiberGrid
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberGrid

#check @SerrePositivity.KST.SConstruction.doubleCofiberRow
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberRow

#check @SerrePositivity.KST.SConstruction.doubleCofiberColumn
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberColumn

#check @SerrePositivity.KST.SConstruction.doubleCofiberGrid_row
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberGrid_row

#check @SerrePositivity.KST.SConstruction.doubleCofiberGrid_column
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberGrid_column

#check @SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_input
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_input

#check @SerrePositivity.KST.SConstruction.cofiberFamilyInput_edge_isInvertible
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyInput_edge_isInvertible

#check @SerrePositivity.KST.SConstruction.doubleCofiberGrid_bottom
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberGrid_bottom

#check @SerrePositivity.KST.SConstruction.doubleCofiberGrid_left
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberGrid_left

#check @SerrePositivity.KST.SConstruction.doubleCofiberGrid_top
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberGrid_top

#check @SerrePositivity.KST.SConstruction.doubleCofiberGrid_right
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberGrid_right

#check @SerrePositivity.KST.SConstruction.functorIsoFlip
#print axioms SerrePositivity.KST.SConstruction.functorIsoFlip

#check @SerrePositivity.KST.SConstruction.functorIsoOfFlip
#print axioms SerrePositivity.KST.SConstruction.functorIsoOfFlip

#check @SerrePositivity.KST.SConstruction.doubleCofiberInputIso
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberInputIso

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_row
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_row

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_column
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_column

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_row_one
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_row_one

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_column_one
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_column_one

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_row_zero_quotient
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_row_zero_quotient

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_column_zero_quotient
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_column_zero_quotient

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_row_zero_isZero
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_row_zero_isZero

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_column_zero_isZero
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_column_zero_isZero

#check @SerrePositivity.KST.SConstruction.functorIsoOfTrivialKanFibrationPostcomp
#print axioms SerrePositivity.KST.SConstruction.functorIsoOfTrivialKanFibrationPostcomp

#check @SerrePositivity.KST.SConstruction.cutRelativeInputIso
#print axioms SerrePositivity.KST.SConstruction.cutRelativeInputIso

#check @SerrePositivity.KST.SConstruction.cutRelativeAmbientIso
#print axioms SerrePositivity.KST.SConstruction.cutRelativeAmbientIso

#check @SerrePositivity.KST.SConstruction.cutRelativeMiddle_comparisonIso
#print axioms SerrePositivity.KST.SConstruction.cutRelativeMiddle_comparisonIso

#check @SerrePositivity.KST.SConstruction.cutRelativeEquivalence
#print axioms SerrePositivity.KST.SConstruction.cutRelativeEquivalence

#check @SerrePositivity.KST.SConstruction.cutLeftSegalEvaluation
#print axioms SerrePositivity.KST.SConstruction.cutLeftSegalEvaluation

#check @SerrePositivity.KST.SConstruction.cutRightSegalEvaluation
#print axioms SerrePositivity.KST.SConstruction.cutRightSegalEvaluation

#check @SerrePositivity.KST.SConstruction.cutRelativeComparison_leftSegal
#print axioms SerrePositivity.KST.SConstruction.cutRelativeComparison_leftSegal

#check @SerrePositivity.KST.SConstruction.cutRelativeComparison_rightSegal
#print axioms SerrePositivity.KST.SConstruction.cutRelativeComparison_rightSegal

#check @SerrePositivity.KST.SConstruction.cutRelativeSegalPair
#print axioms SerrePositivity.KST.SConstruction.cutRelativeSegalPair

#check @SerrePositivity.KST.SConstruction.sPostcompositionFunctorIso
#print axioms SerrePositivity.KST.SConstruction.sPostcompositionFunctorIso

#check @SerrePositivity.KST.SConstruction.StableModelEquivalence
#print axioms SerrePositivity.KST.SConstruction.StableModelEquivalence

#check @SerrePositivity.KST.SConstruction.StableModelEquivalence.toQCatEquivalence
#print axioms SerrePositivity.KST.SConstruction.StableModelEquivalence.toQCatEquivalence

#check @SerrePositivity.KST.SConstruction.StableModelEquivalence.symm
#print axioms SerrePositivity.KST.SConstruction.StableModelEquivalence.symm

#check @SerrePositivity.KST.SConstruction.StableModelEquivalence.sConstruction
#print axioms SerrePositivity.KST.SConstruction.StableModelEquivalence.sConstruction

#check @SerrePositivity.KST.SConstruction.StableModelEquivalence.hom
#print axioms SerrePositivity.KST.SConstruction.StableModelEquivalence.hom

#check @SerrePositivity.KST.SConstruction.StableModelEquivalence.inv
#print axioms SerrePositivity.KST.SConstruction.StableModelEquivalence.inv

#check @SerrePositivity.KST.SConstruction.StableModelEquivalence.homInvIso
#print axioms SerrePositivity.KST.SConstruction.StableModelEquivalence.homInvIso

#check @SerrePositivity.KST.SConstruction.StableModelEquivalence.invHomIso
#print axioms SerrePositivity.KST.SConstruction.StableModelEquivalence.invHomIso

#check @SerrePositivity.KST.SConstruction.objectS_map_localized_isIso_of_equivalence
#print axioms SerrePositivity.KST.SConstruction.objectS_map_localized_isIso_of_equivalence

#check @SerrePositivity.KST.SConstruction.coreSRealization_map_localized_isIso_of_equivalence
#print axioms SerrePositivity.KST.SConstruction.coreSRealization_map_localized_isIso_of_equivalence

#check @SerrePositivity.KST.SConstruction.multiRealization_map_one_localized_isIso_of_equivalence
#print axioms SerrePositivity.KST.SConstruction.multiRealization_map_one_localized_isIso_of_equivalence

#check @SerrePositivity.KST.SConstruction.multiRealization_map_step_localized_isIso_of_equivalence
#print axioms SerrePositivity.KST.SConstruction.multiRealization_map_step_localized_isIso_of_equivalence

#check @SerrePositivity.KST.SConstruction.multiRealization_map_localized_isIso_of_equivalence
#print axioms SerrePositivity.KST.SConstruction.multiRealization_map_localized_isIso_of_equivalence

#check @SerrePositivity.KST.SConstruction.cutRelativeStableEquivalence
#print axioms SerrePositivity.KST.SConstruction.cutRelativeStableEquivalence

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalStableEquivalence
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalStableEquivalence

#check @SerrePositivity.KST.SConstruction.cutRightIntervalStableEquivalence
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalStableEquivalence

#check @SerrePositivity.KST.SConstruction.cutIntervalRestrictions_tensor_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.cutIntervalRestrictions_tensor_localized_isIso

#check @SerrePositivity.KST.SConstruction.cutSegalMap
#print axioms SerrePositivity.KST.SConstruction.cutSegalMap

#check @SerrePositivity.KST.SConstruction.cutSegalMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.cutSegalMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.cutSegalPair_naturality
#print axioms SerrePositivity.KST.SConstruction.cutSegalPair_naturality

#check @SerrePositivity.KST.SConstruction.cutSegalNat
#print axioms SerrePositivity.KST.SConstruction.cutSegalNat

#check @SerrePositivity.KST.SConstruction.cutSegalLocalizedIso
#print axioms SerrePositivity.KST.SConstruction.cutSegalLocalizedIso

#check @SerrePositivity.KST.SConstruction.cutSegalLocalizedIso_app
#print axioms SerrePositivity.KST.SConstruction.cutSegalLocalizedIso_app

#check @SerrePositivity.KST.SConstruction.edgeIntervalInclusion
#print axioms SerrePositivity.KST.SConstruction.edgeIntervalInclusion

#check @SerrePositivity.KST.SConstruction.edgeSegalEvaluation
#print axioms SerrePositivity.KST.SConstruction.edgeSegalEvaluation

#check @SerrePositivity.KST.SConstruction.edgeSegalEvaluation_one
#print axioms SerrePositivity.KST.SConstruction.edgeSegalEvaluation_one

#check @SerrePositivity.KST.SConstruction.cutLeftSegalEvaluation_first
#print axioms SerrePositivity.KST.SConstruction.cutLeftSegalEvaluation_first

#check @SerrePositivity.KST.SConstruction.cutRightSegalEvaluation_edge
#print axioms SerrePositivity.KST.SConstruction.cutRightSegalEvaluation_edge

#check @SerrePositivity.KST.SConstruction.nonemptySSetPower
#print axioms SerrePositivity.KST.SConstruction.nonemptySSetPower

#check @SerrePositivity.KST.SConstruction.nonemptySSetPowerProjection
#print axioms SerrePositivity.KST.SConstruction.nonemptySSetPowerProjection

#check @SerrePositivity.KST.SConstruction.nonemptySSetPowerLift
#print axioms SerrePositivity.KST.SConstruction.nonemptySSetPowerLift

#check @SerrePositivity.KST.SConstruction.nonemptySSetPowerLift_projection
#print axioms SerrePositivity.KST.SConstruction.nonemptySSetPowerLift_projection

#check @SerrePositivity.KST.SConstruction.nonemptySSetPowerLift_comp
#print axioms SerrePositivity.KST.SConstruction.nonemptySSetPowerLift_comp

#check @SerrePositivity.KST.SConstruction.edgeSegalMap
#print axioms SerrePositivity.KST.SConstruction.edgeSegalMap

#check @SerrePositivity.KST.SConstruction.edgeSegalMap_projection
#print axioms SerrePositivity.KST.SConstruction.edgeSegalMap_projection

#check @SerrePositivity.KST.SConstruction.edgeSegalMap_zero
#print axioms SerrePositivity.KST.SConstruction.edgeSegalMap_zero

#check @SerrePositivity.KST.SConstruction.edgeSegalMap_succ
#print axioms SerrePositivity.KST.SConstruction.edgeSegalMap_succ

#check @SerrePositivity.KST.SConstruction.edgeSegalMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.edgeSegalMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.pathFirstEdge_naturality
#print axioms SerrePositivity.KST.SConstruction.pathFirstEdge_naturality

#check @SerrePositivity.KST.SConstruction.pathHeadSegalMap
#print axioms SerrePositivity.KST.SConstruction.pathHeadSegalMap

#check @SerrePositivity.KST.SConstruction.pathHeadSegalMap_fst
#print axioms SerrePositivity.KST.SConstruction.pathHeadSegalMap_fst

#check @SerrePositivity.KST.SConstruction.pathHeadSegalMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.pathHeadSegalMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.pathHeadSegalMap_naturality
#print axioms SerrePositivity.KST.SConstruction.pathHeadSegalMap_naturality

#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary_headPreserving_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary_headPreserving_homotopyPullback

#check @SerrePositivity.KST.SConstruction.trivialKanFibration_of_simplexSurjective_baseChange
#print axioms SerrePositivity.KST.SConstruction.trivialKanFibration_of_simplexSurjective_baseChange

#check @SerrePositivity.KST.SConstruction.fibration_vertex_surjective_of_connected
#print axioms SerrePositivity.KST.SConstruction.fibration_vertex_surjective_of_connected

#check @SerrePositivity.KST.SConstruction.fibration_simplex_surjective_of_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.fibration_simplex_surjective_of_vertex_surjective

#check @SerrePositivity.KST.SConstruction.fibration_simplex_surjective_of_connected
#print axioms SerrePositivity.KST.SConstruction.fibration_simplex_surjective_of_connected

#check @SerrePositivity.KST.SConstruction.localized_isIso_of_simplexSurjective_fibration_baseChange
#print axioms SerrePositivity.KST.SConstruction.localized_isIso_of_simplexSurjective_fibration_baseChange

#check @SerrePositivity.KST.SConstruction.localized_isIso_of_connected_fibration_baseChange
#print axioms SerrePositivity.KST.SConstruction.localized_isIso_of_connected_fibration_baseChange

#check @SerrePositivity.KST.SConstruction.pullbackMapBase_slice_naturality
#print axioms SerrePositivity.KST.SConstruction.pullbackMapBase_slice_naturality

#check @SerrePositivity.KST.SConstruction.localized_isIso_of_connected_baseChange
#print axioms SerrePositivity.KST.SConstruction.localized_isIso_of_connected_baseChange

#check @SerrePositivity.KST.SConstruction.splitBasePullback_projection
#print axioms SerrePositivity.KST.SConstruction.splitBasePullback_projection

#check @SerrePositivity.KST.SConstruction.splitBasePullbackIso
#print axioms SerrePositivity.KST.SConstruction.splitBasePullbackIso

#check @SerrePositivity.KST.SConstruction.homotopyPullback_retraction_of_section
#print axioms SerrePositivity.KST.SConstruction.homotopyPullback_retraction_of_section

#check @SerrePositivity.KST.SConstruction.naturality_homotopyPullback_retraction_of_section_of_kan
#print axioms SerrePositivity.KST.SConstruction.naturality_homotopyPullback_retraction_of_section_of_kan

#check @SerrePositivity.KST.SConstruction.naturality_homotopyPullback_retraction_of_section
#print axioms SerrePositivity.KST.SConstruction.naturality_homotopyPullback_retraction_of_section

#check @SerrePositivity.KST.SConstruction.iteratedSRealizationDiagram_positive_isConnected
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationDiagram_positive_isConnected

#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary_firstFace_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary_firstFace_homotopyPullback

#check @SerrePositivity.KST.SConstruction.naturality_homotopyPullback_id
#print axioms SerrePositivity.KST.SConstruction.naturality_homotopyPullback_id

#check @SerrePositivity.KST.SConstruction.naturality_homotopyPullback_comp
#print axioms SerrePositivity.KST.SConstruction.naturality_homotopyPullback_comp

#check @SerrePositivity.KST.SConstruction.simplicial_naturality_homotopyPullback_of_generators
#print axioms SerrePositivity.KST.SConstruction.simplicial_naturality_homotopyPullback_of_generators

#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary_face_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary_face_homotopyPullback

#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary_degeneracy_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary_degeneracy_homotopyPullback

#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary_homotopyPullback

#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary_realization_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary_realization_homotopyPullback

#check @SerrePositivity.KST.SConstruction.diagonalZeroColumn_eq_rowEvaluation
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroColumn_eq_rowEvaluation

#check @SerrePositivity.KST.SConstruction.diagonalZeroColumn_homotopyPullback_of_zeroRow
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroColumn_homotopyPullback_of_zeroRow

#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary_zeroRow_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary_zeroRow_homotopyPullback

#check @SerrePositivity.KST.SConstruction.iteratedPathToKan
#print axioms SerrePositivity.KST.SConstruction.iteratedPathToKan

#check @SerrePositivity.KST.SConstruction.iteratedRealizationToKan
#print axioms SerrePositivity.KST.SConstruction.iteratedRealizationToKan

#check @SerrePositivity.KST.SConstruction.iteratedPathToKan_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.iteratedPathToKan_localized_isIso

#check @SerrePositivity.KST.SConstruction.iteratedRealizationToKan_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.iteratedRealizationToKan_localized_isIso

#check @SerrePositivity.KST.SConstruction.iteratedBoundaryToKan_comm
#print axioms SerrePositivity.KST.SConstruction.iteratedBoundaryToKan_comm

#check @SerrePositivity.KST.SConstruction.iteratedRealizationToKan_zeroColumn
#print axioms SerrePositivity.KST.SConstruction.iteratedRealizationToKan_zeroColumn

#check @SerrePositivity.KST.SConstruction.zeroRowPathToKan
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathToKan

#check @SerrePositivity.KST.SConstruction.zeroRowPathToKan_boundary
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathToKan_boundary

#check @SerrePositivity.KST.SConstruction.zeroRowKanBoundary_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanBoundary_homotopyPullback

#check @SerrePositivity.KST.SConstruction.basedPathBasepoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.basedPathBasepoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.strictZeroPathFiberMap
#print axioms SerrePositivity.KST.SConstruction.strictZeroPathFiberMap

#check @SerrePositivity.KST.SConstruction.strictZeroPathFiberMap_path
#print axioms SerrePositivity.KST.SConstruction.strictZeroPathFiberMap_path

#check @SerrePositivity.KST.SConstruction.strictZeroPathFiberMap_projection
#print axioms SerrePositivity.KST.SConstruction.strictZeroPathFiberMap_projection

#check @SerrePositivity.KST.SConstruction.strictZeroPathFiberMap_localized_isIso_of_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.strictZeroPathFiberMap_localized_isIso_of_homotopyPullback

#check @SerrePositivity.KST.SConstruction.zeroRowPathFiberComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathFiberComparison

#check @SerrePositivity.KST.SConstruction.zeroRowPathFiberComparison_projection
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathFiberComparison_projection

#check @SerrePositivity.KST.SConstruction.zeroRowPathFiberComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathFiberComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.simplicialPathZeroColumn_section
#print axioms SerrePositivity.KST.SConstruction.simplicialPathZeroColumn_section

#check @SerrePositivity.KST.SConstruction.zeroRowPathToKan_degeneracy
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathToKan_degeneracy

#check @SerrePositivity.KST.SConstruction.zeroRowPathFiberComparison_degeneracy
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathFiberComparison_degeneracy

#check @SerrePositivity.KST.SConstruction.zeroRowPointedModel
#print axioms SerrePositivity.KST.SConstruction.zeroRowPointedModel

#check @SerrePositivity.KST.SConstruction.zeroRowPointedFiberComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowPointedFiberComparison

#check @SerrePositivity.KST.SConstruction.zeroRowPointedFiberComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroRowPointedFiberComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.exists_pointedKanStrictExtension
#print axioms SerrePositivity.KST.SConstruction.exists_pointedKanStrictExtension

#check @SerrePositivity.KST.SConstruction.pointedKanStrictExtension
#print axioms SerrePositivity.KST.SConstruction.pointedKanStrictExtension

#check @SerrePositivity.KST.SConstruction.pointedKanStrictExtension_fac
#print axioms SerrePositivity.KST.SConstruction.pointedKanStrictExtension_fac

#check @SerrePositivity.KST.SConstruction.pointedKanStrictExtension_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.pointedKanStrictExtension_piIsomorphism

#check @SerrePositivity.KST.SConstruction.zeroRowKanFiberComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanFiberComparison

#check @SerrePositivity.KST.SConstruction.zeroRowKanFiberComparison_fac
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanFiberComparison_fac

#check @SerrePositivity.KST.SConstruction.zeroRowKanFiberComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanFiberComparison_piIsomorphism

#check @SerrePositivity.KST.SConstruction.zeroRowPreviousComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowPreviousComparison

#check @SerrePositivity.KST.SConstruction.zeroRowPreviousComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroRowPreviousComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.zeroRowPointedPreviousComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowPointedPreviousComparison

#check @SerrePositivity.KST.SConstruction.zeroRowPointedPreviousComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroRowPointedPreviousComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.zeroRowKanPreviousComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanPreviousComparison

#check @SerrePositivity.KST.SConstruction.zeroRowKanPreviousComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanPreviousComparison_piIsomorphism

#check @SerrePositivity.KST.SConstruction.exists_previousStage_pathFiber_comparison
#print axioms SerrePositivity.KST.SConstruction.exists_previousStage_pathFiber_comparison

#check @SerrePositivity.KST.SConstruction.simplicialFixedSInterchangeNatIso
#print axioms SerrePositivity.KST.SConstruction.simplicialFixedSInterchangeNatIso

#check @SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso
#print axioms SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso

#check @SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso_zero_app
#print axioms SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso_zero_app

#check @SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso_succ_app
#print axioms SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso_succ_app

#check @SerrePositivity.KST.SConstruction.sInterchangeStableIso_sOneComparison_right
#print axioms SerrePositivity.KST.SConstruction.sInterchangeStableIso_sOneComparison_right

#check @SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso_sOneComparison
#print axioms SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso_sOneComparison

#check @SerrePositivity.KST.SConstruction.fixedSInnerCoreDiagram
#print axioms SerrePositivity.KST.SConstruction.fixedSInnerCoreDiagram

#check @SerrePositivity.KST.SConstruction.fixedSOuterCoreDiagram
#print axioms SerrePositivity.KST.SConstruction.fixedSOuterCoreDiagram

#check @SerrePositivity.KST.SConstruction.fixedSCoreDiagramSwapIso
#print axioms SerrePositivity.KST.SConstruction.fixedSCoreDiagramSwapIso

#check @SerrePositivity.KST.SConstruction.fixedSInnerCoreDiagramIso
#print axioms SerrePositivity.KST.SConstruction.fixedSInnerCoreDiagramIso

#check @SerrePositivity.KST.SConstruction.fixedSInnerRealizationIso
#print axioms SerrePositivity.KST.SConstruction.fixedSInnerRealizationIso

#check @SerrePositivity.KST.SConstruction.fixedSOneOuterCoreDiagramIso
#print axioms SerrePositivity.KST.SConstruction.fixedSOneOuterCoreDiagramIso

#check @SerrePositivity.KST.SConstruction.sOneInnerOuterRealizationIso
#print axioms SerrePositivity.KST.SConstruction.sOneInnerOuterRealizationIso

#check @SerrePositivity.KST.SConstruction.sDoubleInclusion
#print axioms SerrePositivity.KST.SConstruction.sDoubleInclusion

#check @SerrePositivity.KST.SConstruction.sDoubleInclusion_mono
#print axioms SerrePositivity.KST.SConstruction.sDoubleInclusion_mono

#check @SerrePositivity.KST.SConstruction.sInterchange_doubleInclusion
#print axioms SerrePositivity.KST.SConstruction.sInterchange_doubleInclusion

#check @SerrePositivity.KST.SConstruction.sDoubleInclusion_postcomp
#print axioms SerrePositivity.KST.SConstruction.sDoubleInclusion_postcomp

#check @SerrePositivity.KST.SConstruction.sDoubleInclusion_outerMap
#print axioms SerrePositivity.KST.SConstruction.sDoubleInclusion_outerMap

#check @SerrePositivity.KST.SConstruction.sDoubleInclusion_innerMap
#print axioms SerrePositivity.KST.SConstruction.sDoubleInclusion_innerMap

#check @SerrePositivity.KST.SConstruction.sInterchangeTransposeDiagram_vertex_ι
#print axioms SerrePositivity.KST.SConstruction.sInterchangeTransposeDiagram_vertex_ι

#check @SerrePositivity.KST.SConstruction.sInterchangeTransposeDiagram_isGapped
#print axioms SerrePositivity.KST.SConstruction.sInterchangeTransposeDiagram_isGapped

#check @SerrePositivity.KST.SConstruction.sInterchange
#print axioms SerrePositivity.KST.SConstruction.sInterchange

#check @SerrePositivity.KST.SConstruction.sInterchange_ι
#print axioms SerrePositivity.KST.SConstruction.sInterchange_ι

#check @SerrePositivity.KST.SConstruction.sInterchange_double_ι
#print axioms SerrePositivity.KST.SConstruction.sInterchange_double_ι

#check @SerrePositivity.KST.SConstruction.sInterchangeStableIso_evaluate_left
#print axioms SerrePositivity.KST.SConstruction.sInterchangeStableIso_evaluate_left

#check @SerrePositivity.KST.SConstruction.sInterchangeStableIso_evaluate_right
#print axioms SerrePositivity.KST.SConstruction.sInterchangeStableIso_evaluate_right

#check @SerrePositivity.KST.SConstruction.sOneComparison_eq_evaluation
#print axioms SerrePositivity.KST.SConstruction.sOneComparison_eq_evaluation

#check @SerrePositivity.KST.SConstruction.sInterchangeStableIso_sOneComparison
#print axioms SerrePositivity.KST.SConstruction.sInterchangeStableIso_sOneComparison

#check @SerrePositivity.KST.SConstruction.sInterchange_twice
#print axioms SerrePositivity.KST.SConstruction.sInterchange_twice

#check @SerrePositivity.KST.SConstruction.sInterchangeIso
#print axioms SerrePositivity.KST.SConstruction.sInterchangeIso

#check @SerrePositivity.KST.SConstruction.sInterchangeStableIso_naturality
#print axioms SerrePositivity.KST.SConstruction.sInterchangeStableIso_naturality

#check @SerrePositivity.KST.SConstruction.sInterchangeEndofunctorIso
#print axioms SerrePositivity.KST.SConstruction.sInterchangeEndofunctorIso

#check @SerrePositivity.KST.SConstruction.sInterchange_outerMap
#print axioms SerrePositivity.KST.SConstruction.sInterchange_outerMap

#check @SerrePositivity.KST.SConstruction.sInterchange_innerMap
#print axioms SerrePositivity.KST.SConstruction.sInterchange_innerMap

#check @SerrePositivity.KST.SConstruction.sInterchangeStableIso
#print axioms SerrePositivity.KST.SConstruction.sInterchangeStableIso

#check @SerrePositivity.KST.SConstruction.sInterchangeRawTranspose
#print axioms SerrePositivity.KST.SConstruction.sInterchangeRawTranspose

#check @SerrePositivity.KST.SConstruction.sInterchangeRawTranspose_vertex
#print axioms SerrePositivity.KST.SConstruction.sInterchangeRawTranspose_vertex

#check @SerrePositivity.KST.SConstruction.sInterchangeRawTranspose_gapped
#print axioms SerrePositivity.KST.SConstruction.sInterchangeRawTranspose_gapped

#check @SerrePositivity.KST.SConstruction.sInterchangeTransposeDiagram
#print axioms SerrePositivity.KST.SConstruction.sInterchangeTransposeDiagram

#check @SerrePositivity.KST.SConstruction.sInterchangeTransposeDiagram_ι
#print axioms SerrePositivity.KST.SConstruction.sInterchangeTransposeDiagram_ι

#check @SerrePositivity.KST.SConstruction.sOneInnerOuterRealizationIso_comparison
#print axioms SerrePositivity.KST.SConstruction.sOneInnerOuterRealizationIso_comparison

#check @SerrePositivity.KST.SConstruction.internalHomSwap_postcomp
#print axioms SerrePositivity.KST.SConstruction.internalHomSwap_postcomp

#check @SerrePositivity.KST.SConstruction.internalHomSwap_pre_left
#print axioms SerrePositivity.KST.SConstruction.internalHomSwap_pre_left

#check @SerrePositivity.KST.SConstruction.diagonalSCyclicInterchangeNatIso
#print axioms SerrePositivity.KST.SConstruction.diagonalSCyclicInterchangeNatIso

#check @SerrePositivity.KST.SConstruction.diagonalSCyclicCoreIso
#print axioms SerrePositivity.KST.SConstruction.diagonalSCyclicCoreIso

#check @SerrePositivity.KST.SConstruction.diagonalOuterSCoreDiagramIso
#print axioms SerrePositivity.KST.SConstruction.diagonalOuterSCoreDiagramIso

#check @SerrePositivity.KST.SConstruction.iteratedSRealizationCyclicIso
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationCyclicIso

#check @SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso_index
#print axioms SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso_index

#check @SerrePositivity.KST.SConstruction.sOneInnerOuterRealizationIso_assembly
#print axioms SerrePositivity.KST.SConstruction.sOneInnerOuterRealizationIso_assembly

#check @SerrePositivity.KST.SConstruction.coordinateZeroInclusion_naturality
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroInclusion_naturality

#check @SerrePositivity.KST.SConstruction.coordinateZeroRange_image_iso
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRange_image_iso

#check @SerrePositivity.KST.SConstruction.coordinateZeroBoundary_image_iso
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroBoundary_image_iso

#check @SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso
#print axioms SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso

#check @SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_zero_app
#print axioms SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_zero_app

#check @SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_succ_app
#print axioms SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_succ_app

#check @SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_diagonal_app
#print axioms SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_diagonal_app

#check @SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_naturality
#print axioms SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_naturality

#check @SerrePositivity.KST.SConstruction.multiCoreSOne_map
#print axioms SerrePositivity.KST.SConstruction.multiCoreSOne_map

#check @SerrePositivity.KST.SConstruction.multiSOneSlideCoreAt
#print axioms SerrePositivity.KST.SConstruction.multiSOneSlideCoreAt

#check @SerrePositivity.KST.SConstruction.multiSOneSlideCoreAt_hom
#print axioms SerrePositivity.KST.SConstruction.multiSOneSlideCoreAt_hom

#check @SerrePositivity.KST.SConstruction.multiSOneSlideCoreAt_naturality
#print axioms SerrePositivity.KST.SConstruction.multiSOneSlideCoreAt_naturality

#check @SerrePositivity.KST.SConstruction.multiSOneSlideCoreIso
#print axioms SerrePositivity.KST.SConstruction.multiSOneSlideCoreIso

#check @SerrePositivity.KST.SConstruction.multiSOneSlideCoreIso_realization
#print axioms SerrePositivity.KST.SConstruction.multiSOneSlideCoreIso_realization

#check @SerrePositivity.KST.SConstruction.sOneInnerOuterRealizationIso_fatBoundary
#print axioms SerrePositivity.KST.SConstruction.sOneInnerOuterRealizationIso_fatBoundary

#check @SerrePositivity.KST.SConstruction.sOneInnerOuterReducedIso
#print axioms SerrePositivity.KST.SConstruction.sOneInnerOuterReducedIso

#check @SerrePositivity.KST.SConstruction.sOneInnerOuterReducedIso_quotient
#print axioms SerrePositivity.KST.SConstruction.sOneInnerOuterReducedIso_quotient

#check @SerrePositivity.KST.SConstruction.sOneInnerOuterReducedIso_comparison
#print axioms SerrePositivity.KST.SConstruction.sOneInnerOuterReducedIso_comparison

#check @SerrePositivity.KST.SConstruction.subcomplexCofiberMap
#print axioms SerrePositivity.KST.SConstruction.subcomplexCofiberMap

#check @SerrePositivity.KST.SConstruction.subcomplexCofiberMap_quotient
#print axioms SerrePositivity.KST.SConstruction.subcomplexCofiberMap_quotient

#check @SerrePositivity.KST.SConstruction.subcomplex_image_iso_inv
#print axioms SerrePositivity.KST.SConstruction.subcomplex_image_iso_inv

#check @SerrePositivity.KST.SConstruction.subcomplexCofiberIso
#print axioms SerrePositivity.KST.SConstruction.subcomplexCofiberIso

#check @SerrePositivity.KST.SConstruction.coordinatePermutationDiagonalIso
#print axioms SerrePositivity.KST.SConstruction.coordinatePermutationDiagonalIso

#check @SerrePositivity.KST.SConstruction.zeroDirectionsIndexEndomorphism_permutation
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsIndexEndomorphism_permutation

#check @SerrePositivity.KST.SConstruction.coordinateZeroRange_permutation
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRange_permutation

#check @SerrePositivity.KST.SConstruction.coordinateZeroBoundary_permutation
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroBoundary_permutation

#check @SerrePositivity.KST.SConstruction.innerVariableOuterMap
#print axioms SerrePositivity.KST.SConstruction.innerVariableOuterMap

#check @SerrePositivity.KST.SConstruction.innerVariableOuterMap_succ
#print axioms SerrePositivity.KST.SConstruction.innerVariableOuterMap_succ

#check @SerrePositivity.KST.SConstruction.innerVariableSComparisonIso_outer_naturality
#print axioms SerrePositivity.KST.SConstruction.innerVariableSComparisonIso_outer_naturality

#check @SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_index
#print axioms SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_index

#check @SerrePositivity.KST.SConstruction.multiMovingSCoreIso_fatBoundary
#print axioms SerrePositivity.KST.SConstruction.multiMovingSCoreIso_fatBoundary

#check @SerrePositivity.KST.SConstruction.multiMovingSBoundaryIso
#print axioms SerrePositivity.KST.SConstruction.multiMovingSBoundaryIso

#check @SerrePositivity.KST.SConstruction.multiMovingSBoundaryIso_quotient
#print axioms SerrePositivity.KST.SConstruction.multiMovingSBoundaryIso_quotient

#check @SerrePositivity.KST.SConstruction.multiInnerSCoreConstruction
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoreConstruction

#check @SerrePositivity.KST.SConstruction.multiOuterSCoreIso
#print axioms SerrePositivity.KST.SConstruction.multiOuterSCoreIso

#check @SerrePositivity.KST.SConstruction.multiMovingSCoreIso
#print axioms SerrePositivity.KST.SConstruction.multiMovingSCoreIso

#check @SerrePositivity.KST.SConstruction.multiInnerSCoreDiagonalIso
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoreDiagonalIso

#check @SerrePositivity.KST.SConstruction.iteratedSMultiInnerRealizationIso
#print axioms SerrePositivity.KST.SConstruction.iteratedSMultiInnerRealizationIso

#check @SerrePositivity.KST.SConstruction.multiMovingSCoreIso_realization
#print axioms SerrePositivity.KST.SConstruction.multiMovingSCoreIso_realization

#check @SerrePositivity.KST.SConstruction.multiHeadSEndofunctor
#print axioms SerrePositivity.KST.SConstruction.multiHeadSEndofunctor

#check @SerrePositivity.KST.SConstruction.multiTailSEndofunctor
#print axioms SerrePositivity.KST.SConstruction.multiTailSEndofunctor

#check @SerrePositivity.KST.SConstruction.multiInnerSEndofunctor
#print axioms SerrePositivity.KST.SConstruction.multiInnerSEndofunctor

#check @SerrePositivity.KST.SConstruction.multiMovingSInterchangeNatIso
#print axioms SerrePositivity.KST.SConstruction.multiMovingSInterchangeNatIso

#check @SerrePositivity.KST.SConstruction.multiInnerSCoordinateRealizationIso_fatBoundary
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoordinateRealizationIso_fatBoundary

#check @SerrePositivity.KST.SConstruction.cyclicRealizationIso
#print axioms SerrePositivity.KST.SConstruction.cyclicRealizationIso

#check @SerrePositivity.KST.SConstruction.cyclicRealizationIso_hom
#print axioms SerrePositivity.KST.SConstruction.cyclicRealizationIso_hom

#check @SerrePositivity.KST.SConstruction.cyclicRealizationIso_fatBoundary
#print axioms SerrePositivity.KST.SConstruction.cyclicRealizationIso_fatBoundary

#check @SerrePositivity.KST.SConstruction.cyclicBoundaryIso
#print axioms SerrePositivity.KST.SConstruction.cyclicBoundaryIso

#check @SerrePositivity.KST.SConstruction.cyclicBoundaryIso_quotient
#print axioms SerrePositivity.KST.SConstruction.cyclicBoundaryIso_quotient

#check @SerrePositivity.KST.SConstruction.cyclicBoundaryIso_coordinate_quotient
#print axioms SerrePositivity.KST.SConstruction.cyclicBoundaryIso_coordinate_quotient

#check @SerrePositivity.KST.SConstruction.innerVariableOuterMap_last
#print axioms SerrePositivity.KST.SConstruction.innerVariableOuterMap_last

#check @SerrePositivity.KST.SConstruction.innerVariableOuterMap_castSucc
#print axioms SerrePositivity.KST.SConstruction.innerVariableOuterMap_castSucc

#check @SerrePositivity.KST.SConstruction.finRotate_castSucc
#print axioms SerrePositivity.KST.SConstruction.finRotate_castSucc

#check @SerrePositivity.KST.SConstruction.innerVariableIndex_obj_permutation
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_obj_permutation

#check @SerrePositivity.KST.SConstruction.innerVariableIndex_map_permutation
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_map_permutation

#check @SerrePositivity.KST.SConstruction.multiInnerSCoordinateCoreIso
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoordinateCoreIso

#check @SerrePositivity.KST.SConstruction.multiInnerSCoordinateRealizationIso
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoordinateRealizationIso

#check @SerrePositivity.KST.SConstruction.multiInnerSCoordinateCoreIso_realization
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoordinateCoreIso_realization

#check @SerrePositivity.KST.SConstruction.multiInnerSCoordinateAt
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoordinateAt

#check @SerrePositivity.KST.SConstruction.multiInnerSCoordinateAt_naturality
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoordinateAt_naturality

#check @SerrePositivity.KST.SConstruction.multiInnerSCoordinateNatIso
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoordinateNatIso

#check @SerrePositivity.KST.SConstruction.simplicialPathCut_zeroRow_boundary
#print axioms SerrePositivity.KST.SConstruction.simplicialPathCut_zeroRow_boundary

#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_zeroRow_boundary
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_zeroRow_boundary

#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_section
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_section

#check @SerrePositivity.KST.SConstruction.rawCofiberCylinderSquare
#print axioms SerrePositivity.KST.SConstruction.rawCofiberCylinderSquare

#check @SerrePositivity.KST.SConstruction.rawCofiberCylinderDesc
#print axioms SerrePositivity.KST.SConstruction.rawCofiberCylinderDesc

#check @SerrePositivity.KST.SConstruction.rawCofiberCylinderDesc_quotient
#print axioms SerrePositivity.KST.SConstruction.rawCofiberCylinderDesc_quotient

#check @SerrePositivity.KST.SConstruction.rawCofiberCylinderDesc_point
#print axioms SerrePositivity.KST.SConstruction.rawCofiberCylinderDesc_point

#check @SerrePositivity.KST.SConstruction.rawCofiberCylinder_hom_ext
#print axioms SerrePositivity.KST.SConstruction.rawCofiberCylinder_hom_ext

#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalBasedContraction
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalBasedContraction

#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_section_quotient
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_section_quotient

#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder

#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder_quotient
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder_quotient

#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder_point
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder_point

#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder_zero
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder_zero

#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder_one
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder_one

#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalContraction
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalContraction

#check @SerrePositivity.KST.SConstruction.zeroRowPathToQuotient_degeneracy
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathToQuotient_degeneracy

#check @SerrePositivity.KST.SConstruction.zeroRowPathContraction_degeneracy
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathContraction_degeneracy

#check @SerrePositivity.KST.SConstruction.zeroRowPathToQuotient
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathToQuotient

#check @SerrePositivity.KST.SConstruction.zeroRowPathContraction
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathContraction

#check @SerrePositivity.KST.SConstruction.zeroRowPathContraction_raw
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathContraction_raw

#check @SerrePositivity.KST.SConstruction.zeroRowPathContraction_zero
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathContraction_zero

#check @SerrePositivity.KST.SConstruction.zeroRowPathContraction_one
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathContraction_one

#check @SerrePositivity.KST.SConstruction.zeroRowPathContractionHomotopy
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathContractionHomotopy

#check @SerrePositivity.KST.SConstruction.zeroRowPathContraction_boundary
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathContraction_boundary

#check @SerrePositivity.KST.SConstruction.cylinder_boundary_constant
#print axioms SerrePositivity.KST.SConstruction.cylinder_boundary_constant

#check @SerrePositivity.KST.SConstruction.circleCylinderDesc_constant_parameter
#print axioms SerrePositivity.KST.SConstruction.circleCylinderDesc_constant_parameter

#check @SerrePositivity.KST.SConstruction.loopOfCylinder_constant_parameter
#print axioms SerrePositivity.KST.SConstruction.loopOfCylinder_constant_parameter

#check @SerrePositivity.KST.SConstruction.circleCylinderDesc
#print axioms SerrePositivity.KST.SConstruction.circleCylinderDesc

#check @SerrePositivity.KST.SConstruction.circleCylinderDesc_quotient
#print axioms SerrePositivity.KST.SConstruction.circleCylinderDesc_quotient

#check @SerrePositivity.KST.SConstruction.circleCylinderDesc_point
#print axioms SerrePositivity.KST.SConstruction.circleCylinderDesc_point

#check @SerrePositivity.KST.SConstruction.loopOfCylinder
#print axioms SerrePositivity.KST.SConstruction.loopOfCylinder

#check @SerrePositivity.KST.SConstruction.loopOfCylinder_uncurry
#print axioms SerrePositivity.KST.SConstruction.loopOfCylinder_uncurry

#check @SerrePositivity.KST.SConstruction.loopOfCylinder_raw
#print axioms SerrePositivity.KST.SConstruction.loopOfCylinder_raw

#check @SerrePositivity.KST.SConstruction.zeroRowBoundaryCylinder
#print axioms SerrePositivity.KST.SConstruction.zeroRowBoundaryCylinder

#check @SerrePositivity.KST.SConstruction.zeroRowBoundaryCylinder_zero
#print axioms SerrePositivity.KST.SConstruction.zeroRowBoundaryCylinder_zero

#check @SerrePositivity.KST.SConstruction.zeroRowBoundaryCylinder_one
#print axioms SerrePositivity.KST.SConstruction.zeroRowBoundaryCylinder_one

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison

#check @SerrePositivity.KST.SConstruction.zeroRowBoundaryCylinder_degeneracy
#print axioms SerrePositivity.KST.SConstruction.zeroRowBoundaryCylinder_degeneracy

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison_degeneracy
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison_degeneracy

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison_raw
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison_raw

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison_assembly
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison_assembly

#check @SerrePositivity.KST.SConstruction.zeroRowPointedLoopComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowPointedLoopComparison

#check @SerrePositivity.KST.SConstruction.zeroRowKanLoopComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanLoopComparison

#check @SerrePositivity.KST.SConstruction.zeroRowKanLoopComparison_unit
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanLoopComparison_unit

#check @SerrePositivity.KST.SConstruction.loop_interval_hom_ext
#print axioms SerrePositivity.KST.SConstruction.loop_interval_hom_ext

#check @SerrePositivity.KST.SConstruction.loopOfCylinder_unique
#print axioms SerrePositivity.KST.SConstruction.loopOfCylinder_unique

#check @SerrePositivity.KST.SConstruction.adjoinTensorMap_first
#print axioms SerrePositivity.KST.SConstruction.adjoinTensorMap_first

#check @SerrePositivity.KST.SConstruction.cofiberSmashProjection_first
#print axioms SerrePositivity.KST.SConstruction.cofiberSmashProjection_first

#check @SerrePositivity.KST.SConstruction.rawCofiberTensorDesc_evaluation
#print axioms SerrePositivity.KST.SConstruction.rawCofiberTensorDesc_evaluation

#check @SerrePositivity.KST.SConstruction.suspensionLoopEquiv_eq_smashCurry
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopEquiv_eq_smashCurry

#check @SerrePositivity.KST.SConstruction.suspensionLoopEquiv_interval
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopEquiv_interval

#check @SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssembly_evaluation
#print axioms SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssembly_evaluation

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjoint_interval
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjoint_interval

#check @SerrePositivity.KST.SConstruction.loop_interval_postcomp
#print axioms SerrePositivity.KST.SConstruction.loop_interval_postcomp

#check @SerrePositivity.KST.SConstruction.kanTargetAssemblyAdjoint_interval
#print axioms SerrePositivity.KST.SConstruction.kanTargetAssemblyAdjoint_interval

#check @SerrePositivity.KST.SConstruction.loop_interval_precomp
#print axioms SerrePositivity.KST.SConstruction.loop_interval_precomp

#check @SerrePositivity.KST.SConstruction.iteratedRealizationToKan_cyclic
#print axioms SerrePositivity.KST.SConstruction.iteratedRealizationToKan_cyclic

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison_assemblyAdjoint
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison_assemblyAdjoint

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison_reducedAssemblyAdjoint
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison_reducedAssemblyAdjoint

#check @SerrePositivity.KST.SConstruction.zeroRowReducedLoopComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowReducedLoopComparison

#check @SerrePositivity.KST.SConstruction.zeroRowReducedLoopComparison_quotient
#print axioms SerrePositivity.KST.SConstruction.zeroRowReducedLoopComparison_quotient

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison_fatBoundary
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison_fatBoundary

#check @SerrePositivity.KST.SConstruction.terminalPointedInterval
#print axioms SerrePositivity.KST.SConstruction.terminalPointedInterval

#check @SerrePositivity.KST.SConstruction.terminalIntervalStart
#print axioms SerrePositivity.KST.SConstruction.terminalIntervalStart

#check @SerrePositivity.KST.SConstruction.terminalIntervalStart_right
#print axioms SerrePositivity.KST.SConstruction.terminalIntervalStart_right

#check @SerrePositivity.KST.SConstruction.terminalIntervalStart_mono
#print axioms SerrePositivity.KST.SConstruction.terminalIntervalStart_mono

#check @SerrePositivity.KST.SConstruction.terminalIntervalStart_inl
#print axioms SerrePositivity.KST.SConstruction.terminalIntervalStart_inl

#check @SerrePositivity.KST.SConstruction.terminalPathSpace
#print axioms SerrePositivity.KST.SConstruction.terminalPathSpace

#check @SerrePositivity.KST.SConstruction.terminalPathSpace_kanComplex
#print axioms SerrePositivity.KST.SConstruction.terminalPathSpace_kanComplex

#check @SerrePositivity.KST.SConstruction.terminalPathStart
#print axioms SerrePositivity.KST.SConstruction.terminalPathStart

#check @SerrePositivity.KST.SConstruction.terminalPathStart_fibration
#print axioms SerrePositivity.KST.SConstruction.terminalPathStart_fibration

#check @SerrePositivity.KST.SConstruction.terminalPathStart_evaluation
#print axioms SerrePositivity.KST.SConstruction.terminalPathStart_evaluation

#check @SerrePositivity.KST.SConstruction.terminalPathFamily_basepoint
#print axioms SerrePositivity.KST.SConstruction.terminalPathFamily_basepoint

#check @SerrePositivity.KST.SConstruction.terminalPathFamily
#print axioms SerrePositivity.KST.SConstruction.terminalPathFamily

#check @SerrePositivity.KST.SConstruction.terminalPathFamily_ι
#print axioms SerrePositivity.KST.SConstruction.terminalPathFamily_ι

#check @SerrePositivity.KST.SConstruction.terminalPathFamily_start
#print axioms SerrePositivity.KST.SConstruction.terminalPathFamily_start

#check @SerrePositivity.KST.SConstruction.terminalPointedInterval_basepoint_anodyne
#print axioms SerrePositivity.KST.SConstruction.terminalPointedInterval_basepoint_anodyne

#check @SerrePositivity.KST.SConstruction.terminalPathSpace_terminal_rlp
#print axioms SerrePositivity.KST.SConstruction.terminalPathSpace_terminal_rlp

#check @SerrePositivity.KST.SConstruction.terminalPathSpace_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.terminalPathSpace_isContractibleKan

#check @SerrePositivity.KST.SConstruction.terminalSuffixReparametrization
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixReparametrization

#check @SerrePositivity.KST.SConstruction.terminalSuffixReparametrization_start
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixReparametrization_start

#check @SerrePositivity.KST.SConstruction.terminalSuffixReparametrization_end
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixReparametrization_end

#check @SerrePositivity.KST.SConstruction.terminalSuffixReparametrization_zero
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixReparametrization_zero

#check @SerrePositivity.KST.SConstruction.terminalSuffixReparametrization_one
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixReparametrization_one

#check @SerrePositivity.KST.SConstruction.terminalSuffixFamily_basepoint
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixFamily_basepoint

#check @SerrePositivity.KST.SConstruction.terminalSuffixFamily
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixFamily

#check @SerrePositivity.KST.SConstruction.terminalSuffixFamily_start
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixFamily_start

#check @SerrePositivity.KST.SConstruction.terminalSuffixFamily_zero
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixFamily_zero

#check @SerrePositivity.KST.SConstruction.terminalSuffixFamily_one
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixFamily_one

#check @SerrePositivity.KST.SConstruction.terminalPathHomotopyFiber
#print axioms SerrePositivity.KST.SConstruction.terminalPathHomotopyFiber

#check @SerrePositivity.KST.SConstruction.terminalPathFamilyFiberMap
#print axioms SerrePositivity.KST.SConstruction.terminalPathFamilyFiberMap

#check @SerrePositivity.KST.SConstruction.terminalStrictZeroFiberMap
#print axioms SerrePositivity.KST.SConstruction.terminalStrictZeroFiberMap

#check @SerrePositivity.KST.SConstruction.terminalFiberCylinder
#print axioms SerrePositivity.KST.SConstruction.terminalFiberCylinder

#check @SerrePositivity.KST.SConstruction.terminalFiberCylinder_zero
#print axioms SerrePositivity.KST.SConstruction.terminalFiberCylinder_zero

#check @SerrePositivity.KST.SConstruction.terminalFiberCylinder_one
#print axioms SerrePositivity.KST.SConstruction.terminalFiberCylinder_one

#check @SerrePositivity.KST.SConstruction.terminalFiberHomotopy
#print axioms SerrePositivity.KST.SConstruction.terminalFiberHomotopy

#check @SerrePositivity.KST.SConstruction.zeroRowPathContraction_terminalBoundary
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathContraction_terminalBoundary

#check @SerrePositivity.KST.SConstruction.zeroRowTerminalFiberComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowTerminalFiberComparison

#check @SerrePositivity.KST.SConstruction.zeroRowTerminalLoopFiberComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowTerminalLoopFiberComparison

#check @SerrePositivity.KST.SConstruction.zeroRowTerminalFiberHomotopy
#print axioms SerrePositivity.KST.SConstruction.zeroRowTerminalFiberHomotopy

#check @SerrePositivity.KST.SConstruction.zeroRowTerminalLoopFiberComparison_projection
#print axioms SerrePositivity.KST.SConstruction.zeroRowTerminalLoopFiberComparison_projection

#check @SerrePositivity.KST.SConstruction.terminalPathBasepoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.terminalPathBasepoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.terminalStrictZeroFiberMap_localized_isIso_of_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.terminalStrictZeroFiberMap_localized_isIso_of_homotopyPullback

#check @SerrePositivity.KST.SConstruction.zeroRowTerminalFiberComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroRowTerminalFiberComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.zeroRowTerminalLoopFiberComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroRowTerminalLoopFiberComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.terminalIntervalStart_swap
#print axioms SerrePositivity.KST.SConstruction.terminalIntervalStart_swap

#check @SerrePositivity.KST.SConstruction.terminalEndpointCircle
#print axioms SerrePositivity.KST.SConstruction.terminalEndpointCircle

#check @SerrePositivity.KST.SConstruction.terminalEndpointCircleToEndpointCircle
#print axioms SerrePositivity.KST.SConstruction.terminalEndpointCircleToEndpointCircle

#check @SerrePositivity.KST.SConstruction.endpointCircleToTerminalEndpointCircle
#print axioms SerrePositivity.KST.SConstruction.endpointCircleToTerminalEndpointCircle

#check @SerrePositivity.KST.SConstruction.terminalEndpointCircleSwapIso
#print axioms SerrePositivity.KST.SConstruction.terminalEndpointCircleSwapIso

#check @SerrePositivity.KST.SConstruction.terminalEndpointCircleIso
#print axioms SerrePositivity.KST.SConstruction.terminalEndpointCircleIso

#check @SerrePositivity.KST.SConstruction.terminalEndpointCircleIso_quotient
#print axioms SerrePositivity.KST.SConstruction.terminalEndpointCircleIso_quotient

#check @SerrePositivity.KST.SConstruction.terminalEndpointCircleMapping_isPullback
#print axioms SerrePositivity.KST.SConstruction.terminalEndpointCircleMapping_isPullback

#check @SerrePositivity.KST.SConstruction.terminalEndpointCircleFiberIso
#print axioms SerrePositivity.KST.SConstruction.terminalEndpointCircleFiberIso

#check @SerrePositivity.KST.SConstruction.loopToTerminalEndpointHomIso
#print axioms SerrePositivity.KST.SConstruction.loopToTerminalEndpointHomIso

#check @SerrePositivity.KST.SConstruction.loopTerminalPathFiberIso
#print axioms SerrePositivity.KST.SConstruction.loopTerminalPathFiberIso

#check @SerrePositivity.KST.SConstruction.loopTerminalPathFiberIso_hom_ι
#print axioms SerrePositivity.KST.SConstruction.loopTerminalPathFiberIso_hom_ι

#check @SerrePositivity.KST.SConstruction.terminalPathStart_basepoint
#print axioms SerrePositivity.KST.SConstruction.terminalPathStart_basepoint

#check @SerrePositivity.KST.SConstruction.loopTerminalBasedPathFiberIso
#print axioms SerrePositivity.KST.SConstruction.loopTerminalBasedPathFiberIso

#check @SerrePositivity.KST.SConstruction.loopTerminalBasedPathFiberIso_hom_ι
#print axioms SerrePositivity.KST.SConstruction.loopTerminalBasedPathFiberIso_hom_ι

#check @SerrePositivity.KST.SConstruction.loopTerminalBasedPathFiberIso_basepoint
#print axioms SerrePositivity.KST.SConstruction.loopTerminalBasedPathFiberIso_basepoint

#check @SerrePositivity.KST.SConstruction.terminalPathHomotopyFiberProjection
#print axioms SerrePositivity.KST.SConstruction.terminalPathHomotopyFiberProjection

#check @SerrePositivity.KST.SConstruction.terminalPathHomotopyFiberProjection_fibration
#print axioms SerrePositivity.KST.SConstruction.terminalPathHomotopyFiberProjection_fibration

#check @SerrePositivity.KST.SConstruction.terminalPathHomotopyFiber_kanComplex
#print axioms SerrePositivity.KST.SConstruction.terminalPathHomotopyFiber_kanComplex

#check @SerrePositivity.KST.SConstruction.loopPointedTerminalPathFiberIso
#print axioms SerrePositivity.KST.SConstruction.loopPointedTerminalPathFiberIso

#check @SerrePositivity.KST.SConstruction.loopToTerminalPathHomotopyFiber
#print axioms SerrePositivity.KST.SConstruction.loopToTerminalPathHomotopyFiber

#check @SerrePositivity.KST.SConstruction.loopToTerminalPathHomotopyFiber_projection
#print axioms SerrePositivity.KST.SConstruction.loopToTerminalPathHomotopyFiber_projection

#check @SerrePositivity.KST.SConstruction.loopToTerminalPathHomotopyFiber_path
#print axioms SerrePositivity.KST.SConstruction.loopToTerminalPathHomotopyFiber_path

#check @SerrePositivity.KST.SConstruction.loopToTerminalPathHomotopyFiber_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.loopToTerminalPathHomotopyFiber_piIsomorphism

#check @SerrePositivity.KST.SConstruction.terminalIntervalToCircle
#print axioms SerrePositivity.KST.SConstruction.terminalIntervalToCircle

#check @SerrePositivity.KST.SConstruction.terminalIntervalToCircle_right
#print axioms SerrePositivity.KST.SConstruction.terminalIntervalToCircle_right

#check @SerrePositivity.KST.SConstruction.loopTerminalRestriction_eq
#print axioms SerrePositivity.KST.SConstruction.loopTerminalRestriction_eq

#check @SerrePositivity.KST.SConstruction.loopTerminalRestriction_family
#print axioms SerrePositivity.KST.SConstruction.loopTerminalRestriction_family

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison_terminalFactor
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison_terminalFactor

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison_terminalComposite_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison_terminalComposite_localized_isIso

#check @SerrePositivity.KST.SConstruction.zeroRowKanLoopComparison_terminalComposite_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanLoopComparison_terminalComposite_piIsomorphism

#check @SerrePositivity.KST.SConstruction.zeroRowKanLoopComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanLoopComparison_piIsomorphism

#check @SerrePositivity.KST.SConstruction.pointed_localized_isIso_of_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.pointed_localized_isIso_of_piIsomorphism

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.kanTargetAssemblyAdjoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.kanTargetAssemblyAdjoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_piIsomorphism

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjoint_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjoint_piIsomorphism

#check @SerrePositivity.KST.SConstruction.boundaryKanSequence_omegaCondition
#print axioms SerrePositivity.KST.SConstruction.boundaryKanSequence_omegaCondition

#check @SerrePositivity.KST.SConstruction.monicBoundaryKanSequence_omegaCondition
#print axioms SerrePositivity.KST.SConstruction.monicBoundaryKanSequence_omegaCondition

#check @SerrePositivity.KST.SConstruction.boundaryOmegaSpectrum
#print axioms SerrePositivity.KST.SConstruction.boundaryOmegaSpectrum

#check @SerrePositivity.KST.SConstruction.kKanSequence_omegaCondition
#print axioms SerrePositivity.KST.SConstruction.kKanSequence_omegaCondition

#check @SerrePositivity.KST.SConstruction.monicKKanSequence_omegaCondition
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequence_omegaCondition

#check @SerrePositivity.KST.SConstruction.kOmegaSpectrum
#print axioms SerrePositivity.KST.SConstruction.kOmegaSpectrum

#check @SerrePositivity.KST.SConstruction.kOmegaSpectrum_zero
#print axioms SerrePositivity.KST.SConstruction.kOmegaSpectrum_zero

#check @SerrePositivity.KST.SConstruction.kOmegaSpectrum_positive_isConnected
#print axioms SerrePositivity.KST.SConstruction.kOmegaSpectrum_positive_isConnected

#check @SerrePositivity.KST.SConstruction.kSpaceSpectrumComparison
#print axioms SerrePositivity.KST.SConstruction.kSpaceSpectrumComparison

#check @SerrePositivity.KST.SConstruction.kSpaceSpectrumComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.kSpaceSpectrumComparison_piIsomorphism

#check @SerrePositivity.KST.SConstruction.kOmegaSpectrum_negative_subsingleton
#print axioms SerrePositivity.KST.SConstruction.kOmegaSpectrum_negative_subsingleton

#check @SerrePositivity.KST.SConstruction.kOmegaSpectrum_negative_eq_one
#print axioms SerrePositivity.KST.SConstruction.kOmegaSpectrum_negative_eq_one

#check @SerrePositivity.KST.SConstruction.kOmegaSpectrum_zeroGroupEquiv
#print axioms SerrePositivity.KST.SConstruction.kOmegaSpectrum_zeroGroupEquiv

#check @SerrePositivity.KST.SConstruction.kOmegaSpectrum_zeroEquivPiZero
#print axioms SerrePositivity.KST.SConstruction.kOmegaSpectrum_zeroEquivPiZero

#check @SerrePositivity.KST.SConstruction.kSpectrumMap
#print axioms SerrePositivity.KST.SConstruction.kSpectrumMap

#check @SerrePositivity.KST.SConstruction.kSpectrumMap_app
#print axioms SerrePositivity.KST.SConstruction.kSpectrumMap_app

#check @SerrePositivity.KST.SConstruction.kSpectrumMap_id_component
#print axioms SerrePositivity.KST.SConstruction.kSpectrumMap_id_component

#check @SerrePositivity.KST.SConstruction.kHomotopyMap
#print axioms SerrePositivity.KST.SConstruction.kHomotopyMap

#check @SerrePositivity.KST.SConstruction.kHomotopyMap_id
#print axioms SerrePositivity.KST.SConstruction.kHomotopyMap_id

#check @SerrePositivity.KST.SConstruction.kHomotopyMap_comp
#print axioms SerrePositivity.KST.SConstruction.kHomotopyMap_comp

#check @SerrePositivity.KST.SConstruction.kHomotopyFunctor
#print axioms SerrePositivity.KST.SConstruction.kHomotopyFunctor

#check @SerrePositivity.KST.SConstruction.kHomotopyStageIso
#print axioms SerrePositivity.KST.SConstruction.kHomotopyStageIso

#check @SerrePositivity.KST.SConstruction.kHomotopyRawStageIso
#print axioms SerrePositivity.KST.SConstruction.kHomotopyRawStageIso

#check @SerrePositivity.KST.SConstruction.kOmegaSpectrum_zeroEquivKSpaceHomotopy
#print axioms SerrePositivity.KST.SConstruction.kOmegaSpectrum_zeroEquivKSpaceHomotopy

#check @SerrePositivity.KST.SConstruction.kOmegaSpectrum_zeroEquivKSpacePiZero
#print axioms SerrePositivity.KST.SConstruction.kOmegaSpectrum_zeroEquivKSpacePiZero

#check @SerrePositivity.KST.SConstruction.boundaryKPiZeroFunctor
#print axioms SerrePositivity.KST.SConstruction.boundaryKPiZeroFunctor

#check @SerrePositivity.KST.SConstruction.rawKZeroHomotopyPiZeroIso
#print axioms SerrePositivity.KST.SConstruction.rawKZeroHomotopyPiZeroIso

#check @SerrePositivity.KST.SConstruction.kHomotopyZeroPiZeroIso
#print axioms SerrePositivity.KST.SConstruction.kHomotopyZeroPiZeroIso

#check @SerrePositivity.KST.SConstruction.coreSOneComparison_piZero_bijective
#print axioms SerrePositivity.KST.SConstruction.coreSOneComparison_piZero_bijective

#check @SerrePositivity.KST.SConstruction.coreSOnePiZeroEquiv
#print axioms SerrePositivity.KST.SConstruction.coreSOnePiZeroEquiv

#check @SerrePositivity.KST.SConstruction.objectCoreVertex
#print axioms SerrePositivity.KST.SConstruction.objectCoreVertex

#check @SerrePositivity.KST.SConstruction.objectKPiZeroClass
#print axioms SerrePositivity.KST.SConstruction.objectKPiZeroClass

#check @SerrePositivity.KST.SConstruction.objectKPiZeroClass_sOne
#print axioms SerrePositivity.KST.SConstruction.objectKPiZeroClass_sOne

#check @SerrePositivity.KST.SConstruction.sOneLoopClass_eq_of_evaluation_eq
#print axioms SerrePositivity.KST.SConstruction.sOneLoopClass_eq_of_evaluation_eq

#check @SerrePositivity.KST.SConstruction.objectKClass
#print axioms SerrePositivity.KST.SConstruction.objectKClass

#check @SerrePositivity.KST.SConstruction.objectKClass_piZero
#print axioms SerrePositivity.KST.SConstruction.objectKClass_piZero

#check @SerrePositivity.KST.SConstruction.objectKPiZeroClass_eq_of_coreClass_eq
#print axioms SerrePositivity.KST.SConstruction.objectKPiZeroClass_eq_of_coreClass_eq

#check @SerrePositivity.KST.SConstruction.objectKClass_eq_of_coreClass_eq
#print axioms SerrePositivity.KST.SConstruction.objectKClass_eq_of_coreClass_eq

#check @SerrePositivity.KST.SConstruction.objectKClass_invertibleSimplex
#print axioms SerrePositivity.KST.SConstruction.objectKClass_invertibleSimplex

#check @SerrePositivity.KST.SConstruction.objectKClass_invertibleEdge
#print axioms SerrePositivity.KST.SConstruction.objectKClass_invertibleEdge

#check @SerrePositivity.KST.SConstruction.objectKClass_iso
#print axioms SerrePositivity.KST.SConstruction.objectKClass_iso

#check @SerrePositivity.KST.SConstruction.homotopyObjectKClass
#print axioms SerrePositivity.KST.SConstruction.homotopyObjectKClass

#check @SerrePositivity.KST.SConstruction.homotopyObjectKClass_mk
#print axioms SerrePositivity.KST.SConstruction.homotopyObjectKClass_mk

#check @SerrePositivity.KST.SConstruction.homotopyObjectKClass_iso
#print axioms SerrePositivity.KST.SConstruction.homotopyObjectKClass_iso

#check @SerrePositivity.KST.SConstruction.kHomotopyZeroPiZeroEquiv_one
#print axioms SerrePositivity.KST.SConstruction.kHomotopyZeroPiZeroEquiv_one

#check @SerrePositivity.KST.SConstruction.sOneComparison_zeroVertex
#print axioms SerrePositivity.KST.SConstruction.sOneComparison_zeroVertex

#check @SerrePositivity.KST.SConstruction.objectKPiZeroClass_of_isZero
#print axioms SerrePositivity.KST.SConstruction.objectKPiZeroClass_of_isZero

#check @SerrePositivity.KST.SConstruction.objectKClass_of_isZero
#print axioms SerrePositivity.KST.SConstruction.objectKClass_of_isZero

#check @SerrePositivity.KST.SConstruction.iteratedRealizationToKan_naturality
#print axioms SerrePositivity.KST.SConstruction.iteratedRealizationToKan_naturality

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison_naturality

#check @SerrePositivity.KST.SConstruction.coreSOnePiZeroEquiv_symm_naturality
#print axioms SerrePositivity.KST.SConstruction.coreSOnePiZeroEquiv_symm_naturality

#check @SerrePositivity.KST.SConstruction.objectKPiZeroClass_naturality
#print axioms SerrePositivity.KST.SConstruction.objectKPiZeroClass_naturality

#check @SerrePositivity.KST.SConstruction.kHomotopyZeroPiZeroEquiv_naturality
#print axioms SerrePositivity.KST.SConstruction.kHomotopyZeroPiZeroEquiv_naturality

#check @SerrePositivity.KST.SConstruction.objectKClass_naturality
#print axioms SerrePositivity.KST.SConstruction.objectKClass_naturality

#check @SerrePositivity.KST.SConstruction.kHomotopyZeroPiZeroEquiv
#print axioms SerrePositivity.KST.SConstruction.kHomotopyZeroPiZeroEquiv

#check @SerrePositivity.KST.SConstruction.kZeroLevelFundamentalGroupEquiv
#print axioms SerrePositivity.KST.SConstruction.kZeroLevelFundamentalGroupEquiv

#check @SerrePositivity.KST.SConstruction.kZeroFundamentalGroupEquiv
#print axioms SerrePositivity.KST.SConstruction.kZeroFundamentalGroupEquiv

#check @SerrePositivity.KST.SConstruction.boundaryFundamentalGroup_mul_comm
#print axioms SerrePositivity.KST.SConstruction.boundaryFundamentalGroup_mul_comm

#check @SerrePositivity.KST.SConstruction.monicKZeroAdjoint_projection
#print axioms SerrePositivity.KST.SConstruction.monicKZeroAdjoint_projection

#check @SerrePositivity.KST.SConstruction.kZeroLevelFundamentalGroupEquiv_apply
#print axioms SerrePositivity.KST.SConstruction.kZeroLevelFundamentalGroupEquiv_apply

#check @SerrePositivity.KST.SConstruction.kZeroFundamentalGroupEquiv_apply
#print axioms SerrePositivity.KST.SConstruction.kZeroFundamentalGroupEquiv_apply

#check @SerrePositivity.KST.SConstruction.kHomotopyZeroPiZeroEquiv_formula
#print axioms SerrePositivity.KST.SConstruction.kHomotopyZeroPiZeroEquiv_formula

#check @SerrePositivity.KST.SConstruction.kZeroFundamentalGroupEquiv_objectKClass
#print axioms SerrePositivity.KST.SConstruction.kZeroFundamentalGroupEquiv_objectKClass

#check @SerrePositivity.KST.SConstruction.objectBoundaryKanComparison
#print axioms SerrePositivity.KST.SConstruction.objectBoundaryKanComparison

#check @SerrePositivity.KST.SConstruction.objectBoundaryKanComparison_vertex
#print axioms SerrePositivity.KST.SConstruction.objectBoundaryKanComparison_vertex

#check @SerrePositivity.KST.SConstruction.objectBoundaryEdge
#print axioms SerrePositivity.KST.SConstruction.objectBoundaryEdge

#check @SerrePositivity.KST.SConstruction.objectBoundaryTriangle
#print axioms SerrePositivity.KST.SConstruction.objectBoundaryTriangle

#check @SerrePositivity.KST.SConstruction.objectBoundaryTriangle_mul
#print axioms SerrePositivity.KST.SConstruction.objectBoundaryTriangle_mul

#check @SerrePositivity.KST.SConstruction.diagonalObjectInclusion_simplex
#print axioms SerrePositivity.KST.SConstruction.diagonalObjectInclusion_simplex

#check @SerrePositivity.KST.SConstruction.objectToCoreSRealization_simplex
#print axioms SerrePositivity.KST.SConstruction.objectToCoreSRealization_simplex

#check @SerrePositivity.KST.SConstruction.objectBoundaryEdge_loop
#print axioms SerrePositivity.KST.SConstruction.objectBoundaryEdge_loop

#check @SerrePositivity.KST.SConstruction.objectBoundaryEdge_objectKClass
#print axioms SerrePositivity.KST.SConstruction.objectBoundaryEdge_objectKClass

#check @SerrePositivity.KST.SConstruction.objectKClass_sTwo
#print axioms SerrePositivity.KST.SConstruction.objectKClass_sTwo

#check @SerrePositivity.KST.SConstruction.sTwoFace_middle
#print axioms SerrePositivity.KST.SConstruction.sTwoFace_middle

#check @SerrePositivity.KST.SConstruction.sTwoFace_subobject
#print axioms SerrePositivity.KST.SConstruction.sTwoFace_subobject

#check @SerrePositivity.KST.SConstruction.sTwoFace_quotient
#print axioms SerrePositivity.KST.SConstruction.sTwoFace_quotient

#check @SerrePositivity.KST.SConstruction.objectKClass_cofiber
#print axioms SerrePositivity.KST.SConstruction.objectKClass_cofiber

#check @SerrePositivity.KST.SConstruction.cofiberDiagramOfZeroTriangle
#print axioms SerrePositivity.KST.SConstruction.cofiberDiagramOfZeroTriangle

#check @SerrePositivity.KST.SConstruction.homotopyObjectKClass_cofiberTriangle
#print axioms SerrePositivity.KST.SConstruction.homotopyObjectKClass_cofiberTriangle

#check @SerrePositivity.KST.SConstruction.homotopyObjectKClass_triangle
#print axioms SerrePositivity.KST.SConstruction.homotopyObjectKClass_triangle

#check @SerrePositivity.KST.SConstruction.triangulatedKZeroMap
#print axioms SerrePositivity.KST.SConstruction.triangulatedKZeroMap

#check @SerrePositivity.KST.SConstruction.triangulatedKZeroMap_mk
#print axioms SerrePositivity.KST.SConstruction.triangulatedKZeroMap_mk

#check @SerrePositivity.KST.SConstruction.triangulatedKZeroMap_vertex
#print axioms SerrePositivity.KST.SConstruction.triangulatedKZeroMap_vertex

#check @SerrePositivity.KST.SConstruction.stableModelHom_exact
#print axioms SerrePositivity.KST.SConstruction.stableModelHom_exact

#check @SerrePositivity.KST.SConstruction.triangulatedKZeroSourceMap
#print axioms SerrePositivity.KST.SConstruction.triangulatedKZeroSourceMap

#check @SerrePositivity.KST.SConstruction.triangulatedKZeroSourceMap_mk
#print axioms SerrePositivity.KST.SConstruction.triangulatedKZeroSourceMap_mk

#check @SerrePositivity.KST.SConstruction.homotopyObjectKClass_naturality
#print axioms SerrePositivity.KST.SConstruction.homotopyObjectKClass_naturality

#check @SerrePositivity.KST.SConstruction.triangulatedKZeroMap_naturality
#print axioms SerrePositivity.KST.SConstruction.triangulatedKZeroMap_naturality

#check @SerrePositivity.KST.SConstruction.fundamentalNerveTranspose
#print axioms SerrePositivity.KST.SConstruction.fundamentalNerveTranspose

#check @SerrePositivity.KST.SConstruction.fundamentalNerveUntranspose
#print axioms SerrePositivity.KST.SConstruction.fundamentalNerveUntranspose

#check @SerrePositivity.KST.SConstruction.fundamentalNerveUntranspose_transpose
#print axioms SerrePositivity.KST.SConstruction.fundamentalNerveUntranspose_transpose

#check @SerrePositivity.KST.SConstruction.fundamentalNerveTranspose_untranspose
#print axioms SerrePositivity.KST.SConstruction.fundamentalNerveTranspose_untranspose

#check @SerrePositivity.KST.SConstruction.fundamentalNerveTranspose_pre
#print axioms SerrePositivity.KST.SConstruction.fundamentalNerveTranspose_pre

#check @SerrePositivity.KST.SConstruction.fundamentalNerveUntranspose_pre
#print axioms SerrePositivity.KST.SConstruction.fundamentalNerveUntranspose_pre

#check @SerrePositivity.KST.SConstruction.fundamentalNerveTranspose_post
#print axioms SerrePositivity.KST.SConstruction.fundamentalNerveTranspose_post

#check @SerrePositivity.KST.SConstruction.fundamentalNerveUntranspose_post
#print axioms SerrePositivity.KST.SConstruction.fundamentalNerveUntranspose_post

#check @SerrePositivity.KST.SConstruction.fundamentalGroupoidNerve_kanComplex
#print axioms SerrePositivity.KST.SConstruction.fundamentalGroupoidNerve_kanComplex

#check @SerrePositivity.KST.SConstruction.fundamentalNerveUntranspose_eq
#print axioms SerrePositivity.KST.SConstruction.fundamentalNerveUntranspose_eq

#check @SerrePositivity.KST.SConstruction.fundamentalNerveUntransposeHomotopy
#print axioms SerrePositivity.KST.SConstruction.fundamentalNerveUntransposeHomotopy

#check @SerrePositivity.KST.SConstruction.simplicialFundamentalGroupoid
#print axioms SerrePositivity.KST.SConstruction.simplicialFundamentalGroupoid

#check @SerrePositivity.KST.SConstruction.fundamentalGroupoidNerveUnit
#print axioms SerrePositivity.KST.SConstruction.fundamentalGroupoidNerveUnit

#check @SerrePositivity.KST.SConstruction.fundamentalGroupoidComparison
#print axioms SerrePositivity.KST.SConstruction.fundamentalGroupoidComparison

#check @SerrePositivity.KST.SConstruction.fundamentalGroupoidComparison_fac
#print axioms SerrePositivity.KST.SConstruction.fundamentalGroupoidComparison_fac

#check @SerrePositivity.KST.SConstruction.exists_fundamentalGroupoidExtension
#print axioms SerrePositivity.KST.SConstruction.exists_fundamentalGroupoidExtension

#check @SerrePositivity.KST.SConstruction.fundamentalGroupoidExtension
#print axioms SerrePositivity.KST.SConstruction.fundamentalGroupoidExtension

#check @SerrePositivity.KST.SConstruction.fundamentalGroupoidExtension_fac
#print axioms SerrePositivity.KST.SConstruction.fundamentalGroupoidExtension_fac

#check @SerrePositivity.KST.SConstruction.fundamentalGroupoidInverse
#print axioms SerrePositivity.KST.SConstruction.fundamentalGroupoidInverse

#check @SerrePositivity.KST.SConstruction.fundamentalGroupoidInverse_pre
#print axioms SerrePositivity.KST.SConstruction.fundamentalGroupoidInverse_pre

#check @SerrePositivity.KST.SConstruction.fundamentalGroupoidComparison_leftInverse
#print axioms SerrePositivity.KST.SConstruction.fundamentalGroupoidComparison_leftInverse

#check @SerrePositivity.KST.SConstruction.fundamentalGroupoidComparison_right_restriction
#print axioms SerrePositivity.KST.SConstruction.fundamentalGroupoidComparison_right_restriction

#check @SerrePositivity.KST.SConstruction.fundamentalGroupoidComparison_rightInverse
#print axioms SerrePositivity.KST.SConstruction.fundamentalGroupoidComparison_rightInverse

#check @SerrePositivity.KST.SConstruction.fundamentalGroupoidEquivalence
#print axioms SerrePositivity.KST.SConstruction.fundamentalGroupoidEquivalence

#check @SerrePositivity.KST.SConstruction.fundamentalGroupoidComparison_fullyFaithful
#print axioms SerrePositivity.KST.SConstruction.fundamentalGroupoidComparison_fullyFaithful

#check @SerrePositivity.KST.SConstruction.fundamentalGroupoidComparison_map_surjective
#print axioms SerrePositivity.KST.SConstruction.fundamentalGroupoidComparison_map_surjective

#check @SerrePositivity.KST.SConstruction.fundamentalGroupoidComparison_map_injective
#print axioms SerrePositivity.KST.SConstruction.fundamentalGroupoidComparison_map_injective

#check @SerrePositivity.KST.SConstruction.simplicialFundamentalGroupoid_hom_rec
#print axioms SerrePositivity.KST.SConstruction.simplicialFundamentalGroupoid_hom_rec

#check @SerrePositivity.KST.SConstruction.kanAnodyne_hom_rec
#print axioms SerrePositivity.KST.SConstruction.kanAnodyne_hom_rec

#check @SerrePositivity.KST.SConstruction.fundamentalLoopEdge
#print axioms SerrePositivity.KST.SConstruction.fundamentalLoopEdge

#check @SerrePositivity.KST.SConstruction.fundamentalLoopSimplex
#print axioms SerrePositivity.KST.SConstruction.fundamentalLoopSimplex

#check @SerrePositivity.KST.SConstruction.fundamentalLoopEdgeEquiv
#print axioms SerrePositivity.KST.SConstruction.fundamentalLoopEdgeEquiv

#check @SerrePositivity.KST.SConstruction.fundamentalLoopEdge_const
#print axioms SerrePositivity.KST.SConstruction.fundamentalLoopEdge_const

#check @SerrePositivity.KST.SConstruction.fundamentalLoopMulToComp
#print axioms SerrePositivity.KST.SConstruction.fundamentalLoopMulToComp

#check @SerrePositivity.KST.SConstruction.fundamentalLoopCompToMul
#print axioms SerrePositivity.KST.SConstruction.fundamentalLoopCompToMul

#check @SerrePositivity.KST.SConstruction.fundamentalLoop_rel_iff
#print axioms SerrePositivity.KST.SConstruction.fundamentalLoop_rel_iff

#check @SerrePositivity.KST.SConstruction.fundamentalLoopToEdgeHom
#print axioms SerrePositivity.KST.SConstruction.fundamentalLoopToEdgeHom

#check @SerrePositivity.KST.SConstruction.fundamentalLoopToEdgeHom_bijective
#print axioms SerrePositivity.KST.SConstruction.fundamentalLoopToEdgeHom_bijective

#check @SerrePositivity.KST.SConstruction.fundamentalLoopHomEquiv
#print axioms SerrePositivity.KST.SConstruction.fundamentalLoopHomEquiv

#check @SerrePositivity.KST.SConstruction.fundamentalLoopHomEquiv_mk
#print axioms SerrePositivity.KST.SConstruction.fundamentalLoopHomEquiv_mk

#check @SerrePositivity.KST.SConstruction.fundamentalLoopHomEquiv_one
#print axioms SerrePositivity.KST.SConstruction.fundamentalLoopHomEquiv_one

#check @SerrePositivity.KST.SConstruction.fundamentalLoopHomEquiv_mul
#print axioms SerrePositivity.KST.SConstruction.fundamentalLoopHomEquiv_mul

#check @SerrePositivity.KST.SConstruction.fundamentalLoopHomEquiv_isIso
#print axioms SerrePositivity.KST.SConstruction.fundamentalLoopHomEquiv_isIso

#check @SerrePositivity.KST.SConstruction.fundamentalLoopHomEquiv_inv
#print axioms SerrePositivity.KST.SConstruction.fundamentalLoopHomEquiv_inv

#check @SerrePositivity.KST.SConstruction.fundamentalLoopEdge_mapSimplex
#print axioms SerrePositivity.KST.SConstruction.fundamentalLoopEdge_mapSimplex

#check @SerrePositivity.KST.SConstruction.kanAnodyneLoopPresentation
#print axioms SerrePositivity.KST.SConstruction.kanAnodyneLoopPresentation

#check @SerrePositivity.KST.SConstruction.kanAnodyneLoopPresentation_apply
#print axioms SerrePositivity.KST.SConstruction.kanAnodyneLoopPresentation_apply

#check @SerrePositivity.KST.SConstruction.kanAnodyneLoopPresentation_symm_apply
#print axioms SerrePositivity.KST.SConstruction.kanAnodyneLoopPresentation_symm_apply

#check @SerrePositivity.KST.SConstruction.kanAnodyneLoopPresentation_mk
#print axioms SerrePositivity.KST.SConstruction.kanAnodyneLoopPresentation_mk

#check @SerrePositivity.KST.SConstruction.kanAnodyneLoopPresentation_one
#print axioms SerrePositivity.KST.SConstruction.kanAnodyneLoopPresentation_one

#check @SerrePositivity.KST.SConstruction.kanAnodyneLoopPresentation_mul
#print axioms SerrePositivity.KST.SConstruction.kanAnodyneLoopPresentation_mul

#check @SerrePositivity.KST.SConstruction.kanAnodyneLoopPresentation_inv
#print axioms SerrePositivity.KST.SConstruction.kanAnodyneLoopPresentation_inv

#check @SerrePositivity.KST.SConstruction.boundaryFundamentalGroupoid
#print axioms SerrePositivity.KST.SConstruction.boundaryFundamentalGroupoid

#check @SerrePositivity.KST.SConstruction.boundaryFundamentalBasepoint
#print axioms SerrePositivity.KST.SConstruction.boundaryFundamentalBasepoint

#check @SerrePositivity.KST.SConstruction.kZeroGroupoidPresentation
#print axioms SerrePositivity.KST.SConstruction.kZeroGroupoidPresentation

#check @SerrePositivity.KST.SConstruction.kZeroGroupoidPresentation_one
#print axioms SerrePositivity.KST.SConstruction.kZeroGroupoidPresentation_one

#check @SerrePositivity.KST.SConstruction.kZeroGroupoidPresentation_mul
#print axioms SerrePositivity.KST.SConstruction.kZeroGroupoidPresentation_mul

#check @SerrePositivity.KST.SConstruction.kZeroGroupoidPresentation_inv
#print axioms SerrePositivity.KST.SConstruction.kZeroGroupoidPresentation_inv

#check @SerrePositivity.KST.SConstruction.objectRawBoundaryComparison
#print axioms SerrePositivity.KST.SConstruction.objectRawBoundaryComparison

#check @SerrePositivity.KST.SConstruction.objectRawBoundaryComparison_kan
#print axioms SerrePositivity.KST.SConstruction.objectRawBoundaryComparison_kan

#check @SerrePositivity.KST.SConstruction.iteratedZeroColumn_boundary_zero
#print axioms SerrePositivity.KST.SConstruction.iteratedZeroColumn_boundary_zero

#check @SerrePositivity.KST.SConstruction.objectRawBoundaryComparison_vertex
#print axioms SerrePositivity.KST.SConstruction.objectRawBoundaryComparison_vertex

#check @SerrePositivity.KST.SConstruction.objectRawBoundaryEdge
#print axioms SerrePositivity.KST.SConstruction.objectRawBoundaryEdge

#check @SerrePositivity.KST.SConstruction.objectRawBoundaryEdge_kan
#print axioms SerrePositivity.KST.SConstruction.objectRawBoundaryEdge_kan

#check @SerrePositivity.KST.SConstruction.objectBoundaryPath
#print axioms SerrePositivity.KST.SConstruction.objectBoundaryPath

#check @SerrePositivity.KST.SConstruction.kZeroGroupoidPresentation_objectKClass
#print axioms SerrePositivity.KST.SConstruction.kZeroGroupoidPresentation_objectKClass

#check @SerrePositivity.KST.SConstruction.rawCofiber_simplex_cases
#print axioms SerrePositivity.KST.SConstruction.rawCofiber_simplex_cases

#check @SerrePositivity.KST.SConstruction.boundaryReducedRealization_vertex_eq
#print axioms SerrePositivity.KST.SConstruction.boundaryReducedRealization_vertex_eq

#check @SerrePositivity.KST.SConstruction.boundaryReducedRealization_vertex_subsingleton
#print axioms SerrePositivity.KST.SConstruction.boundaryReducedRealization_vertex_subsingleton

#check @SerrePositivity.KST.SConstruction.rawBoundaryLoopSimplex
#print axioms SerrePositivity.KST.SConstruction.rawBoundaryLoopSimplex

#check @SerrePositivity.KST.SConstruction.diagonalAssembly_diagonalSimplex
#print axioms SerrePositivity.KST.SConstruction.diagonalAssembly_diagonalSimplex

#check @SerrePositivity.KST.SConstruction.assemblyEdgeParameterTriangle
#print axioms SerrePositivity.KST.SConstruction.assemblyEdgeParameterTriangle

#check @SerrePositivity.KST.SConstruction.assemblyEdgeParameterTriangle_face_zero
#print axioms SerrePositivity.KST.SConstruction.assemblyEdgeParameterTriangle_face_zero

#check @SerrePositivity.KST.SConstruction.assemblyEdgeParameterTriangle_face_one
#print axioms SerrePositivity.KST.SConstruction.assemblyEdgeParameterTriangle_face_one

#check @SerrePositivity.KST.SConstruction.assemblyEdgeParameterTriangle_face_two
#print axioms SerrePositivity.KST.SConstruction.assemblyEdgeParameterTriangle_face_two

#check @SerrePositivity.KST.SConstruction.assemblyEdgeTriangle
#print axioms SerrePositivity.KST.SConstruction.assemblyEdgeTriangle

#check @SerrePositivity.KST.SConstruction.assemblyEdgeTriangle_face_one
#print axioms SerrePositivity.KST.SConstruction.assemblyEdgeTriangle_face_one

#check @SerrePositivity.KST.SConstruction.assemblyEdge_start_constant
#print axioms SerrePositivity.KST.SConstruction.assemblyEdge_start_constant

#check @SerrePositivity.KST.SConstruction.assemblyEdgeTriangle_face_two
#print axioms SerrePositivity.KST.SConstruction.assemblyEdgeTriangle_face_two

#check @SerrePositivity.KST.SConstruction.assemblyEdgeTriangle_face_zero
#print axioms SerrePositivity.KST.SConstruction.assemblyEdgeTriangle_face_zero

#check @SerrePositivity.KST.SConstruction.rawBoundaryPath
#print axioms SerrePositivity.KST.SConstruction.rawBoundaryPath

#check @SerrePositivity.KST.SConstruction.objectRawBoundaryEdge_assembly
#print axioms SerrePositivity.KST.SConstruction.objectRawBoundaryEdge_assembly

#check @SerrePositivity.KST.SConstruction.rawBoundaryDiagonalTriangle
#print axioms SerrePositivity.KST.SConstruction.rawBoundaryDiagonalTriangle

#check @SerrePositivity.KST.SConstruction.rawBoundaryPath_diagonal
#print axioms SerrePositivity.KST.SConstruction.rawBoundaryPath_diagonal

#check @SerrePositivity.KST.SConstruction.rawBoundary_point_edge
#print axioms SerrePositivity.KST.SConstruction.rawBoundary_point_edge

#check @SerrePositivity.KST.SConstruction.rawBoundaryLoopSimplex_degenerate
#print axioms SerrePositivity.KST.SConstruction.rawBoundaryLoopSimplex_degenerate

#check @SerrePositivity.KST.SConstruction.rawBoundaryPath_point
#print axioms SerrePositivity.KST.SConstruction.rawBoundaryPath_point

#check @SerrePositivity.KST.SConstruction.rawBoundaryPath_cases
#print axioms SerrePositivity.KST.SConstruction.rawBoundaryPath_cases

#check @SerrePositivity.KST.SConstruction.singletonCategoryHom
#print axioms SerrePositivity.KST.SConstruction.singletonCategoryHom

#check @SerrePositivity.KST.SConstruction.singletonCategoryHom_self
#print axioms SerrePositivity.KST.SConstruction.singletonCategoryHom_self

#check @SerrePositivity.KST.SConstruction.singletonCategoryHom_comp
#print axioms SerrePositivity.KST.SConstruction.singletonCategoryHom_comp

#check @SerrePositivity.KST.SConstruction.singletonCategoryHom_inv
#print axioms SerrePositivity.KST.SConstruction.singletonCategoryHom_inv

#check @SerrePositivity.KST.SConstruction.boundaryFundamentalGroupoid_obj_eq
#print axioms SerrePositivity.KST.SConstruction.boundaryFundamentalGroupoid_obj_eq

#check @SerrePositivity.KST.SConstruction.boundaryFundamentalGroupoid_subsingleton
#print axioms SerrePositivity.KST.SConstruction.boundaryFundamentalGroupoid_subsingleton

#check @SerrePositivity.KST.SConstruction.singletonCategoryHom_boundary_edge
#print axioms SerrePositivity.KST.SConstruction.singletonCategoryHom_boundary_edge

#check @SerrePositivity.KST.SConstruction.boundaryPathKClass
#print axioms SerrePositivity.KST.SConstruction.boundaryPathKClass

#check @SerrePositivity.KST.SConstruction.boundaryPathKClass_id
#print axioms SerrePositivity.KST.SConstruction.boundaryPathKClass_id

#check @SerrePositivity.KST.SConstruction.boundaryPathKClass_comp
#print axioms SerrePositivity.KST.SConstruction.boundaryPathKClass_comp

#check @SerrePositivity.KST.SConstruction.boundaryPathKClass_inv
#print axioms SerrePositivity.KST.SConstruction.boundaryPathKClass_inv

#check @SerrePositivity.KST.SConstruction.boundaryPathKClass_object
#print axioms SerrePositivity.KST.SConstruction.boundaryPathKClass_object

#check @SerrePositivity.KST.SConstruction.boundaryPathKClass_presentation
#print axioms SerrePositivity.KST.SConstruction.boundaryPathKClass_presentation

#check @SerrePositivity.KST.SConstruction.boundaryPathKClass_mem_triangulatedKZeroRange
#print axioms SerrePositivity.KST.SConstruction.boundaryPathKClass_mem_triangulatedKZeroRange

#check @SerrePositivity.KST.SConstruction.triangulatedKZeroMap_surjective
#print axioms SerrePositivity.KST.SConstruction.triangulatedKZeroMap_surjective

#check @SerrePositivity.KST.SConstruction.objectTriangulatedClass
#print axioms SerrePositivity.KST.SConstruction.objectTriangulatedClass

#check @SerrePositivity.KST.SConstruction.cofiberStableEvaluation_vertex
#print axioms SerrePositivity.KST.SConstruction.cofiberStableEvaluation_vertex

#check @SerrePositivity.KST.SConstruction.sOneComparison_gappedDiagram_vertex
#print axioms SerrePositivity.KST.SConstruction.sOneComparison_gappedDiagram_vertex

#check @SerrePositivity.KST.SConstruction.cofiberTriangulatedClass_additivity
#print axioms SerrePositivity.KST.SConstruction.cofiberTriangulatedClass_additivity

#check @SerrePositivity.KST.SConstruction.objectTriangulatedClass_sTwo
#print axioms SerrePositivity.KST.SConstruction.objectTriangulatedClass_sTwo

#check @SerrePositivity.KST.SConstruction.sOneComparison_degenerate_isZero
#print axioms SerrePositivity.KST.SConstruction.sOneComparison_degenerate_isZero

#check @SerrePositivity.KST.SConstruction.objectTriangulatedClass_degenerate
#print axioms SerrePositivity.KST.SConstruction.objectTriangulatedClass_degenerate

#check @SerrePositivity.KST.SConstruction.triangulatedKZeroDelooping
#print axioms SerrePositivity.KST.SConstruction.triangulatedKZeroDelooping

#check @SerrePositivity.KST.SConstruction.objectTriangulatedFunctor
#print axioms SerrePositivity.KST.SConstruction.objectTriangulatedFunctor

#check @SerrePositivity.KST.SConstruction.objectTriangulatedFunctor_map_edge
#print axioms SerrePositivity.KST.SConstruction.objectTriangulatedFunctor_map_edge

#check @SerrePositivity.KST.SConstruction.objectTriangulatedGroupoidFunctor
#print axioms SerrePositivity.KST.SConstruction.objectTriangulatedGroupoidFunctor

#check @SerrePositivity.KST.SConstruction.objectTriangulatedNerveMap
#print axioms SerrePositivity.KST.SConstruction.objectTriangulatedNerveMap

#check @SerrePositivity.KST.SConstruction.objectTriangulatedNerveTarget_isGroupoid
#print axioms SerrePositivity.KST.SConstruction.objectTriangulatedNerveTarget_isGroupoid

#check @SerrePositivity.KST.SConstruction.objectTriangulatedNerveMap_untranspose
#print axioms SerrePositivity.KST.SConstruction.objectTriangulatedNerveMap_untranspose

#check @SerrePositivity.KST.SConstruction.objectRawBoundaryComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.objectRawBoundaryComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.exists_rawBoundaryTriangulatedMap
#print axioms SerrePositivity.KST.SConstruction.exists_rawBoundaryTriangulatedMap

#check @SerrePositivity.KST.SConstruction.rawBoundaryTriangulatedMap
#print axioms SerrePositivity.KST.SConstruction.rawBoundaryTriangulatedMap

#check @SerrePositivity.KST.SConstruction.rawBoundaryTriangulatedHomotopy
#print axioms SerrePositivity.KST.SConstruction.rawBoundaryTriangulatedHomotopy

#check @SerrePositivity.KST.SConstruction.exists_boundaryKanTriangulatedMap
#print axioms SerrePositivity.KST.SConstruction.exists_boundaryKanTriangulatedMap

#check @SerrePositivity.KST.SConstruction.boundaryKanTriangulatedMap
#print axioms SerrePositivity.KST.SConstruction.boundaryKanTriangulatedMap

#check @SerrePositivity.KST.SConstruction.boundaryKanTriangulatedMap_unit
#print axioms SerrePositivity.KST.SConstruction.boundaryKanTriangulatedMap_unit

#check @SerrePositivity.KST.SConstruction.kanLoopSingleObjAddHom
#print axioms SerrePositivity.KST.SConstruction.kanLoopSingleObjAddHom

#check @SerrePositivity.KST.SConstruction.kanLoopSingleObjAddHom_mk
#print axioms SerrePositivity.KST.SConstruction.kanLoopSingleObjAddHom_mk

#check @SerrePositivity.KST.SConstruction.kanLoopSingleObjAddHom_inv_mk
#print axioms SerrePositivity.KST.SConstruction.kanLoopSingleObjAddHom_inv_mk

#check @SerrePositivity.KST.SConstruction.kZeroToTriangulatedMap
#print axioms SerrePositivity.KST.SConstruction.kZeroToTriangulatedMap

#check @SerrePositivity.KST.SConstruction.kZeroToTriangulatedMap_apply
#print axioms SerrePositivity.KST.SConstruction.kZeroToTriangulatedMap_apply

#check @SerrePositivity.KST.SConstruction.kZeroToTriangulatedMap_object_formula
#print axioms SerrePositivity.KST.SConstruction.kZeroToTriangulatedMap_object_formula

#check @SerrePositivity.KST.SConstruction.arOne_isFrame
#print axioms SerrePositivity.KST.SConstruction.arOne_isFrame

#check @SerrePositivity.KST.SConstruction.exists_strictZeroSOneDiagram
#print axioms SerrePositivity.KST.SConstruction.exists_strictZeroSOneDiagram

#check @SerrePositivity.KST.SConstruction.arZero_hom_ext
#print axioms SerrePositivity.KST.SConstruction.arZero_hom_ext

#check @SerrePositivity.KST.SConstruction.exists_closedObjectSOne
#print axioms SerrePositivity.KST.SConstruction.exists_closedObjectSOne

#check @SerrePositivity.KST.SConstruction.singleObj_loop_naturality
#print axioms SerrePositivity.KST.SConstruction.singleObj_loop_naturality

#check @SerrePositivity.KST.SConstruction.singleObj_edge_value_congr
#print axioms SerrePositivity.KST.SConstruction.singleObj_edge_value_congr

#check @SerrePositivity.KST.SConstruction.boundaryKanTriangulatedMap_closed_edge
#print axioms SerrePositivity.KST.SConstruction.boundaryKanTriangulatedMap_closed_edge

#check @SerrePositivity.KST.SConstruction.kZeroToTriangulatedMap_object
#print axioms SerrePositivity.KST.SConstruction.kZeroToTriangulatedMap_object

#check @SerrePositivity.KST.SConstruction.kZeroToTriangulatedMap_left_inverse
#print axioms SerrePositivity.KST.SConstruction.kZeroToTriangulatedMap_left_inverse

#check @SerrePositivity.KST.SConstruction.kZeroToTriangulatedMap_right_inverse
#print axioms SerrePositivity.KST.SConstruction.kZeroToTriangulatedMap_right_inverse

#check @SerrePositivity.KST.SConstruction.triangulatedKZeroEquiv
#print axioms SerrePositivity.KST.SConstruction.triangulatedKZeroEquiv

#check @SerrePositivity.KST.SConstruction.triangulatedKZeroEquiv_vertex
#print axioms SerrePositivity.KST.SConstruction.triangulatedKZeroEquiv_vertex

#check @SerrePositivity.KST.SConstruction.triangulatedKZeroEquiv_naturality
#print axioms SerrePositivity.KST.SConstruction.triangulatedKZeroEquiv_naturality

#check @SerrePositivity.KST.SConstruction.kZeroToTriangulatedMap_naturality
#print axioms SerrePositivity.KST.SConstruction.kZeroToTriangulatedMap_naturality

#check @SerrePositivity.KST.SConstruction.triangulatedKZeroSourceMap_id
#print axioms SerrePositivity.KST.SConstruction.triangulatedKZeroSourceMap_id

#check @SerrePositivity.KST.SConstruction.triangulatedKZeroSourceMap_comp
#print axioms SerrePositivity.KST.SConstruction.triangulatedKZeroSourceMap_comp

#check @SerrePositivity.KST.SConstruction.triangulatedKZeroFunctor
#print axioms SerrePositivity.KST.SConstruction.triangulatedKZeroFunctor

#check @SerrePositivity.KST.SConstruction.kZeroAdditiveFunctor
#print axioms SerrePositivity.KST.SConstruction.kZeroAdditiveFunctor

#check @SerrePositivity.KST.SConstruction.triangulatedKZeroNatIso
#print axioms SerrePositivity.KST.SConstruction.triangulatedKZeroNatIso

#check @SerrePositivity.KST.SConstruction.triangulatedKZeroPiZeroIso
#print axioms SerrePositivity.KST.SConstruction.triangulatedKZeroPiZeroIso

#check @SerrePositivity.KST.SConstruction.pointedMappingTransport
#print axioms SerrePositivity.KST.SConstruction.pointedMappingTransport

#check @SerrePositivity.KST.SConstruction.pointedMappingTransport_vertex
#print axioms SerrePositivity.KST.SConstruction.pointedMappingTransport_vertex

#check @SerrePositivity.KST.SConstruction.pointedMappingTransport_id
#print axioms SerrePositivity.KST.SConstruction.pointedMappingTransport_id

#check @SerrePositivity.KST.SConstruction.pointedMappingTransport_comp
#print axioms SerrePositivity.KST.SConstruction.pointedMappingTransport_comp

#check @SerrePositivity.KST.SConstruction.pointedMappingTransport_restriction
#print axioms SerrePositivity.KST.SConstruction.pointedMappingTransport_restriction

#check @SerrePositivity.KST.SConstruction.pointedExtensionTransport
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionTransport

#check @SerrePositivity.KST.SConstruction.pointedExtensionTransport_projection
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionTransport_projection

#check @SerrePositivity.KST.SConstruction.pointedExtensionTransport_vertex
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionTransport_vertex

#check @SerrePositivity.KST.SConstruction.pointedExtensionTransport_id
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionTransport_id

#check @SerrePositivity.KST.SConstruction.pointedExtensionTransport_comp
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionTransport_comp

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedChoices
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedChoices

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedChoices_isContractibleKan

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedChoices_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedChoices_relative_lifting

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedFromSource
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedFromSource

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedFromTarget
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedFromTarget

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedMap
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedMap

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedFromSource_map
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedFromSource_map

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedFromTarget_map
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedFromTarget_map

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedPost
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedPost

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedPre
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedPre

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedChoices_nonempty_edge
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedChoices_nonempty_edge

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedChoices_fill_boundary
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedChoices_fill_boundary

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedPost_source
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedPost_source

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedPre_target
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedPre_target

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixed_middle
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixed_middle

#check @SerrePositivity.KST.SConstruction.triangleEdgeFaces_compatible
#print axioms SerrePositivity.KST.SConstruction.triangleEdgeFaces_compatible

#check @SerrePositivity.KST.SConstruction.contractibleKan_nonempty_compStruct
#print axioms SerrePositivity.KST.SConstruction.contractibleKan_nonempty_compStruct

#check @SerrePositivity.KST.SConstruction.kanAssemblyCompositionFirstEdge
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCompositionFirstEdge

#check @SerrePositivity.KST.SConstruction.kanAssemblyCompositionSecondEdge
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCompositionSecondEdge

#check @SerrePositivity.KST.SConstruction.kanAssemblyCompositionTriangle_nonempty
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCompositionTriangle_nonempty

#check @SerrePositivity.KST.SConstruction.pointedLiftSpace
#print axioms SerrePositivity.KST.SConstruction.pointedLiftSpace

#check @SerrePositivity.KST.SConstruction.pointedLiftSpace_projection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.pointedLiftSpace_projection_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.pointedLiftSpace_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.pointedLiftSpace_isContractibleKan

#check @SerrePositivity.KST.SConstruction.pointedLiftSpace_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.pointedLiftSpace_relative_lifting

#check @SerrePositivity.KST.SConstruction.pointedLiftMap
#print axioms SerrePositivity.KST.SConstruction.pointedLiftMap

#check @SerrePositivity.KST.SConstruction.pointedLiftMap_fac
#print axioms SerrePositivity.KST.SConstruction.pointedLiftMap_fac

#check @SerrePositivity.KST.SConstruction.pointedMappingPathSectionSpace
#print axioms SerrePositivity.KST.SConstruction.pointedMappingPathSectionSpace

#check @SerrePositivity.KST.SConstruction.pointedMappingPathSectionSpace_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.pointedMappingPathSectionSpace_isContractibleKan

#check @SerrePositivity.KST.SConstruction.pointedMappingPathInverseAt
#print axioms SerrePositivity.KST.SConstruction.pointedMappingPathInverseAt

#check @SerrePositivity.KST.SConstruction.pointedMappingPathInverseFamily
#print axioms SerrePositivity.KST.SConstruction.pointedMappingPathInverseFamily

#check @SerrePositivity.KST.SConstruction.pointedMappingPathInverseFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.pointedMappingPathInverseFamily_vertex

#check @SerrePositivity.KST.SConstruction.pointedMappingPathInverseAt_homotopy
#print axioms SerrePositivity.KST.SConstruction.pointedMappingPathInverseAt_homotopy

#check @SerrePositivity.KST.SConstruction.pointedMappingPathSectionSpace_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.pointedMappingPathSectionSpace_relative_lifting

#check @SerrePositivity.KST.SConstruction.oneDirectionKanInverseChoices
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanInverseChoices

#check @SerrePositivity.KST.SConstruction.oneDirectionKanInverseChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanInverseChoices_isContractibleKan

#check @SerrePositivity.KST.SConstruction.oneDirectionKanInverseAt
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanInverseAt

#check @SerrePositivity.KST.SConstruction.oneDirectionKanInverseAt_component
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanInverseAt_component

#check @SerrePositivity.KST.SConstruction.oneDirectionKanInverseChoices_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanInverseChoices_relative_lifting

#check @SerrePositivity.KST.SConstruction.freePathMap_endpoint
#print axioms SerrePositivity.KST.SConstruction.freePathMap_endpoint

#check @SerrePositivity.KST.SConstruction.mappingPathTransport
#print axioms SerrePositivity.KST.SConstruction.mappingPathTransport

#check @SerrePositivity.KST.SConstruction.mappingPathTransport_path
#print axioms SerrePositivity.KST.SConstruction.mappingPathTransport_path

#check @SerrePositivity.KST.SConstruction.mappingPathTransport_retraction
#print axioms SerrePositivity.KST.SConstruction.mappingPathTransport_retraction

#check @SerrePositivity.KST.SConstruction.mappingPathTransport_projection
#print axioms SerrePositivity.KST.SConstruction.mappingPathTransport_projection

#check @SerrePositivity.KST.SConstruction.mappingPathTransport_id
#print axioms SerrePositivity.KST.SConstruction.mappingPathTransport_id

#check @SerrePositivity.KST.SConstruction.mappingPathTransport_comp
#print axioms SerrePositivity.KST.SConstruction.mappingPathTransport_comp

#check @SerrePositivity.KST.SConstruction.pointedMappingTransport_post
#print axioms SerrePositivity.KST.SConstruction.pointedMappingTransport_post

#check @SerrePositivity.KST.SConstruction.pointedLiftTransport
#print axioms SerrePositivity.KST.SConstruction.pointedLiftTransport

#check @SerrePositivity.KST.SConstruction.pointedLiftTransport_projection
#print axioms SerrePositivity.KST.SConstruction.pointedLiftTransport_projection

#check @SerrePositivity.KST.SConstruction.pointedLiftTransport_vertex
#print axioms SerrePositivity.KST.SConstruction.pointedLiftTransport_vertex

#check @SerrePositivity.KST.SConstruction.pointedLiftTransport_id
#print axioms SerrePositivity.KST.SConstruction.pointedLiftTransport_id

#check @SerrePositivity.KST.SConstruction.pointedLiftTransport_comp
#print axioms SerrePositivity.KST.SConstruction.pointedLiftTransport_comp

#check @SerrePositivity.KST.SConstruction.oneDirectionMappingPathMap
#print axioms SerrePositivity.KST.SConstruction.oneDirectionMappingPathMap

#check @SerrePositivity.KST.SConstruction.oneDirectionMappingPathMap_id
#print axioms SerrePositivity.KST.SConstruction.oneDirectionMappingPathMap_id

#check @SerrePositivity.KST.SConstruction.oneDirectionMappingPathMap_comp
#print axioms SerrePositivity.KST.SConstruction.oneDirectionMappingPathMap_comp

#check @SerrePositivity.KST.SConstruction.oneDirectionMappingPathFunctor
#print axioms SerrePositivity.KST.SConstruction.oneDirectionMappingPathFunctor

#check @SerrePositivity.KST.SConstruction.oneDirectionMappingPathMap_projection
#print axioms SerrePositivity.KST.SConstruction.oneDirectionMappingPathMap_projection

#check @SerrePositivity.KST.SConstruction.oneDirectionMappingPathMap_retraction
#print axioms SerrePositivity.KST.SConstruction.oneDirectionMappingPathMap_retraction

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedChoices
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedChoices

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedChoices_isContractibleKan

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedChoices_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedChoices_relative_lifting

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFromSource
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFromSource

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFromTarget
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFromTarget

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedMap
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedMap

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFamily
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFamily

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFromSource_map
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFromSource_map

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFromTarget_map
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFromTarget_map

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFamily_vertex

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedChoices_nonempty_edge
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedChoices_nonempty_edge

#check @SerrePositivity.KST.SConstruction.oneDirectionKanInverseAt_naturality_edge
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanInverseAt_naturality_edge

#check @SerrePositivity.KST.SConstruction.oneDirectionKanInverseAt_naturality_homotopy
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanInverseAt_naturality_homotopy

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedPost
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedPost

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedPre
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedPre

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedPost_source
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedPost_source

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedPre_target
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedPre_target

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixed_middle
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixed_middle

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCompositionFirstEdge
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCompositionFirstEdge

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCompositionSecondEdge
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCompositionSecondEdge

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCompositionTriangle_nonempty
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCompositionTriangle_nonempty

#check @SerrePositivity.KST.SConstruction.pointedMappingComposition
#print axioms SerrePositivity.KST.SConstruction.pointedMappingComposition

#check @SerrePositivity.KST.SConstruction.pointedMappingComposition_vertex
#print axioms SerrePositivity.KST.SConstruction.pointedMappingComposition_vertex

#check @SerrePositivity.KST.SConstruction.pointedMappingComposition_pre
#print axioms SerrePositivity.KST.SConstruction.pointedMappingComposition_pre

#check @SerrePositivity.KST.SConstruction.pointedMappingComposition_post
#print axioms SerrePositivity.KST.SConstruction.pointedMappingComposition_post

#check @SerrePositivity.KST.SConstruction.pointedMappingComposition_middle
#print axioms SerrePositivity.KST.SConstruction.pointedMappingComposition_middle

#check @SerrePositivity.KST.SConstruction.pointedMappingComposition_families_middle
#print axioms SerrePositivity.KST.SConstruction.pointedMappingComposition_families_middle

#check @SerrePositivity.KST.SConstruction.pointedMappingComposition_families_post
#print axioms SerrePositivity.KST.SConstruction.pointedMappingComposition_families_post

#check @SerrePositivity.KST.SConstruction.pointedMappingComposition_families_pre
#print axioms SerrePositivity.KST.SConstruction.pointedMappingComposition_families_pre

#check @SerrePositivity.KST.SConstruction.contractibleKan_tensor
#print axioms SerrePositivity.KST.SConstruction.contractibleKan_tensor

#check @SerrePositivity.KST.SConstruction.contractibleKan_tensor_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.contractibleKan_tensor_relative_lifting

#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointFamily
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointFamily

#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointFamily_vertex

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyChoices
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyChoices

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyChoices_isContractibleKan

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyChoices_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyChoices_relative_lifting

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjointAt
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjointAt

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjointFamily
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjointFamily

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjointFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjointFamily_vertex

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjointAt_component
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjointAt_component

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjointAt_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjointAt_piIsomorphism

#check @SerrePositivity.KST.SConstruction.pointedMappingTransport_source_id
#print axioms SerrePositivity.KST.SConstruction.pointedMappingTransport_source_id

#check @SerrePositivity.KST.SConstruction.pointedMappingTransport_target_id
#print axioms SerrePositivity.KST.SConstruction.pointedMappingTransport_target_id

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedFamily
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedFamily

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedFamily_source
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedFamily_source

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedFamily_target
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedFamily_target

#check @SerrePositivity.KST.SConstruction.pointedLiftTransport_evaluation
#print axioms SerrePositivity.KST.SConstruction.pointedLiftTransport_evaluation

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFamily_source
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFamily_source

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFamily_target
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFamily_target

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyExtensionFamily
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyExtensionFamily

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyInverseFamily
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyInverseFamily

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyExtensionMiddle
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyExtensionMiddle

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyInverseMiddle
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyInverseMiddle

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilies_middle
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilies_middle

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyExtensionSource
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyExtensionSource

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyInverseTarget
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyInverseTarget

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilies_source
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilies_source

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilies_target
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilies_target

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinder
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinder

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinderFamily
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinderFamily

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinderFamily_left
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinderFamily_left

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinderFamily_right
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinderFamily_right

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinderSource
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinderSource

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinderTarget
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinderTarget

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinderFamily_source
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinderFamily_source

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinderFamily_target
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinderFamily_target

#check @SerrePositivity.KST.SConstruction.contractibleKan_toUnit_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.contractibleKan_toUnit_localized_isIso

#check @SerrePositivity.KST.SConstruction.pointDoubleCylinder_toUnit_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.pointDoubleCylinder_toUnit_localized_isIso

#check @SerrePositivity.KST.SConstruction.doubleCylinder_toUnit_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.doubleCylinder_toUnit_localized_isIso

#check @SerrePositivity.KST.SConstruction.kanReplacement_contractible_of_localized_toUnit
#print axioms SerrePositivity.KST.SConstruction.kanReplacement_contractible_of_localized_toUnit

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityParameters
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityParameters

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityParameterUnit
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityParameterUnit

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityParameters_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityParameters_isContractibleKan

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityParameters_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityParameters_relative_lifting

#check @SerrePositivity.KST.SConstruction.exists_boundaryAssemblyNaturalityFamily
#print axioms SerrePositivity.KST.SConstruction.exists_boundaryAssemblyNaturalityFamily

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamily
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamily

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamily_unit
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamily_unit

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalitySource
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalitySource

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityTarget
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityTarget

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamily_source
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamily_source

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamily_target
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamily_target

#check @SerrePositivity.KST.SConstruction.anodyneExtensionChoices
#print axioms SerrePositivity.KST.SConstruction.anodyneExtensionChoices

#check @SerrePositivity.KST.SConstruction.anodyneExtensionChoices_projection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.anodyneExtensionChoices_projection_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.anodyneExtensionChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.anodyneExtensionChoices_isContractibleKan

#check @SerrePositivity.KST.SConstruction.anodyneExtensionChoices_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.anodyneExtensionChoices_relative_lifting

#check @SerrePositivity.KST.SConstruction.anodyneExtensionAt
#print axioms SerrePositivity.KST.SConstruction.anodyneExtensionAt

#check @SerrePositivity.KST.SConstruction.anodyneExtensionAt_fac
#print axioms SerrePositivity.KST.SConstruction.anodyneExtensionAt_fac

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyChoices
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyChoices

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyChoices_isContractibleKan

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyChoices_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyChoices_relative_lifting

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyAt
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyAt

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyAt_unit
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyAt_unit

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyAt_source
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyAt_source

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyAt_target
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyAt_target

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyAt_source_vertex
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyAt_source_vertex

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyAt_target_vertex
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFamilyAt_target_vertex

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjointAt_naturality_edge
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjointAt_naturality_edge

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjointAt_naturality_homotopy
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjointAt_naturality_homotopy

#check @SerrePositivity.KST.SConstruction.cartesianEdgePair
#print axioms SerrePositivity.KST.SConstruction.cartesianEdgePair

#check @SerrePositivity.KST.SConstruction.cartesianEdgeCompStruct
#print axioms SerrePositivity.KST.SConstruction.cartesianEdgeCompStruct

#check @SerrePositivity.KST.SConstruction.cartesianEdgeLowerTriangle
#print axioms SerrePositivity.KST.SConstruction.cartesianEdgeLowerTriangle

#check @SerrePositivity.KST.SConstruction.cartesianEdgeUpperTriangle
#print axioms SerrePositivity.KST.SConstruction.cartesianEdgeUpperTriangle

#check @SerrePositivity.KST.SConstruction.cartesianEdgeInterchange
#print axioms SerrePositivity.KST.SConstruction.cartesianEdgeInterchange

#check @SerrePositivity.KST.SConstruction.cartesianLeftParameterEdge
#print axioms SerrePositivity.KST.SConstruction.cartesianLeftParameterEdge

#check @SerrePositivity.KST.SConstruction.cartesianRightParameterEdge
#print axioms SerrePositivity.KST.SConstruction.cartesianRightParameterEdge

#check @SerrePositivity.KST.SConstruction.cartesianLeftParameterEdge_evaluation
#print axioms SerrePositivity.KST.SConstruction.cartesianLeftParameterEdge_evaluation

#check @SerrePositivity.KST.SConstruction.cartesianRightParameterEdge_evaluation
#print axioms SerrePositivity.KST.SConstruction.cartesianRightParameterEdge_evaluation

#check @SerrePositivity.KST.SConstruction.contractibleKan_parallel_homMk
#print axioms SerrePositivity.KST.SConstruction.contractibleKan_parallel_homMk

#check @SerrePositivity.KST.SConstruction.contractibleKan_three_edge_fac
#print axioms SerrePositivity.KST.SConstruction.contractibleKan_three_edge_fac

#check @SerrePositivity.KST.SConstruction.contractibleKan_mapped_parallel_homMk
#print axioms SerrePositivity.KST.SConstruction.contractibleKan_mapped_parallel_homMk

#check @SerrePositivity.KST.SConstruction.contractibleKan_mapped_compStruct
#print axioms SerrePositivity.KST.SConstruction.contractibleKan_mapped_compStruct

#check @SerrePositivity.KST.SConstruction.nonemptyCompStruct_of_homMk_fac
#print axioms SerrePositivity.KST.SConstruction.nonemptyCompStruct_of_homMk_fac

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityEdgeAt
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityEdgeAt

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityEdgeAt_parallel
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityEdgeAt_parallel

#check @SerrePositivity.KST.SConstruction.doubleCylinderMiddleEdge
#print axioms SerrePositivity.KST.SConstruction.doubleCylinderMiddleEdge

#check @SerrePositivity.KST.SConstruction.doubleCylinderMiddleEdge_constant_evaluation
#print axioms SerrePositivity.KST.SConstruction.doubleCylinderMiddleEdge_constant_evaluation

#check @SerrePositivity.KST.SConstruction.doubleCylinderMiddleMappedEdge
#print axioms SerrePositivity.KST.SConstruction.doubleCylinderMiddleMappedEdge

#check @SerrePositivity.KST.SConstruction.doubleCylinderMiddleMappedEdge_constant_evaluation
#print axioms SerrePositivity.KST.SConstruction.doubleCylinderMiddleMappedEdge_constant_evaluation

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyLeftMiddle
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyLeftMiddle

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyRightMiddle
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyRightMiddle

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyExtensionParameterEdge
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyExtensionParameterEdge

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyInverseParameterEdge
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyInverseParameterEdge

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyMiddleParameterEdge
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyMiddleParameterEdge

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinderFamily_middle
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityCylinderFamily_middle

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyMiddleParameterEdge_evaluation
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyMiddleParameterEdge_evaluation

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyExtensionParameterEdge_evaluation
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyExtensionParameterEdge_evaluation

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyInverseParameterEdge_evaluation
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyInverseParameterEdge_evaluation

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyCanonicalPath_fac
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyCanonicalPath_fac

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyCanonicalPath_evaluated_fac
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyCanonicalPath_evaluated_fac

#check @SerrePositivity.KST.SConstruction.assemblyCrossedFamily
#print axioms SerrePositivity.KST.SConstruction.assemblyCrossedFamily

#check @SerrePositivity.KST.SConstruction.assemblyCrossedFamily_edge_interchange
#print axioms SerrePositivity.KST.SConstruction.assemblyCrossedFamily_edge_interchange

#check @SerrePositivity.KST.SConstruction.assemblyCrossedFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.assemblyCrossedFamily_vertex

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedFamily_post
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedFamily_post

#check @SerrePositivity.KST.SConstruction.kanAssemblyMixedFamily_pre
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyMixedFamily_pre

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFamily_post
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFamily_post

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFamily_pre
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseMixedFamily_pre

#check @SerrePositivity.KST.SConstruction.assemblyCrossedFamily_extension_source
#print axioms SerrePositivity.KST.SConstruction.assemblyCrossedFamily_extension_source

#check @SerrePositivity.KST.SConstruction.assemblyCrossedFamily_inverse_target
#print axioms SerrePositivity.KST.SConstruction.assemblyCrossedFamily_inverse_target

#check @SerrePositivity.KST.SConstruction.assemblyCrossedFamily_inverse_source
#print axioms SerrePositivity.KST.SConstruction.assemblyCrossedFamily_inverse_source

#check @SerrePositivity.KST.SConstruction.assemblyCrossedFamily_extension_target
#print axioms SerrePositivity.KST.SConstruction.assemblyCrossedFamily_extension_target

#check @SerrePositivity.KST.SConstruction.edge_source_eq_of_edge_eq
#print axioms SerrePositivity.KST.SConstruction.edge_source_eq_of_edge_eq

#check @SerrePositivity.KST.SConstruction.edge_target_eq_of_edge_eq
#print axioms SerrePositivity.KST.SConstruction.edge_target_eq_of_edge_eq

#check @SerrePositivity.KST.SConstruction.contractibleKan_mapped_three_edge_triangle
#print axioms SerrePositivity.KST.SConstruction.contractibleKan_mapped_three_edge_triangle

#check @SerrePositivity.KST.SConstruction.exists_mapped_factorization
#print axioms SerrePositivity.KST.SConstruction.exists_mapped_factorization

#check @SerrePositivity.KST.SConstruction.nonemptyCompStruct_paste_factorizations
#print axioms SerrePositivity.KST.SConstruction.nonemptyCompStruct_paste_factorizations

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyIntermediateVertex
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyIntermediateVertex

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyExtensionEdgeAt
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyExtensionEdgeAt

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyInverseEdgeAt
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyInverseEdgeAt

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyExtensionEdgeAt_evaluation
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyExtensionEdgeAt_evaluation

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyInverseEdgeAt_evaluation
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyInverseEdgeAt_evaluation

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFactorizationTriangle_nonempty
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityFactorizationTriangle_nonempty

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyExtensionFamily_post
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyExtensionFamily_post

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyInverseFamily_pre
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyInverseFamily_pre

#check @SerrePositivity.KST.SConstruction.mappedEdge_square
#print axioms SerrePositivity.KST.SConstruction.mappedEdge_square

#check @SerrePositivity.KST.SConstruction.cartesianLeftFamilyEdge_square
#print axioms SerrePositivity.KST.SConstruction.cartesianLeftFamilyEdge_square

#check @SerrePositivity.KST.SConstruction.cartesianRightFamilyEdge_square
#print axioms SerrePositivity.KST.SConstruction.cartesianRightFamilyEdge_square

#check @SerrePositivity.KST.SConstruction.cartesianLeftFamilyEdge_parameter
#print axioms SerrePositivity.KST.SConstruction.cartesianLeftFamilyEdge_parameter

#check @SerrePositivity.KST.SConstruction.cartesianRightFamilyEdge_parameter
#print axioms SerrePositivity.KST.SConstruction.cartesianRightFamilyEdge_parameter

#check @SerrePositivity.KST.SConstruction.cartesianLeftFamilyEdge_moving
#print axioms SerrePositivity.KST.SConstruction.cartesianLeftFamilyEdge_moving

#check @SerrePositivity.KST.SConstruction.cartesianRightFamilyEdge_moving
#print axioms SerrePositivity.KST.SConstruction.cartesianRightFamilyEdge_moving

#check @SerrePositivity.KST.SConstruction.mappedEdge_family_congr
#print axioms SerrePositivity.KST.SConstruction.mappedEdge_family_congr

#check @SerrePositivity.KST.SConstruction.cartesianLeftFamilyEdge_congr
#print axioms SerrePositivity.KST.SConstruction.cartesianLeftFamilyEdge_congr

#check @SerrePositivity.KST.SConstruction.cartesianRightFamilyEdge_congr
#print axioms SerrePositivity.KST.SConstruction.cartesianRightFamilyEdge_congr

#check @SerrePositivity.KST.SConstruction.pointedNaturalityCompositionFirstEdge
#print axioms SerrePositivity.KST.SConstruction.pointedNaturalityCompositionFirstEdge

#check @SerrePositivity.KST.SConstruction.pointedNaturalityCompositionSecondEdge
#print axioms SerrePositivity.KST.SConstruction.pointedNaturalityCompositionSecondEdge

#check @SerrePositivity.KST.SConstruction.nonemptyCompStruct_paste_factorization_diagram
#print axioms SerrePositivity.KST.SConstruction.nonemptyCompStruct_paste_factorization_diagram

#check @SerrePositivity.KST.SConstruction.BoundaryAssemblyNaturalityData
#print axioms SerrePositivity.KST.SConstruction.BoundaryAssemblyNaturalityData

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityData_nonempty
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNaturalityData_nonempty

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyChosenNaturalityEdge
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyChosenNaturalityEdge

#check @SerrePositivity.KST.SConstruction.kanAssemblyCompositionFirstEdge_edge
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCompositionFirstEdge_edge

#check @SerrePositivity.KST.SConstruction.kanAssemblyCompositionSecondEdge_edge
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCompositionSecondEdge_edge

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCompositionFirstEdge_edge
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCompositionFirstEdge_edge

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCompositionSecondEdge_edge
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCompositionSecondEdge_edge

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyCompositionTriangle_nonempty
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyCompositionTriangle_nonempty

#check @SerrePositivity.KST.SConstruction.assemblyHomBifunctor
#print axioms SerrePositivity.KST.SConstruction.assemblyHomBifunctor

#check @SerrePositivity.KST.SConstruction.AssemblyInputArrow
#print axioms SerrePositivity.KST.SConstruction.AssemblyInputArrow

#check @SerrePositivity.KST.SConstruction.assemblyArrowSource
#print axioms SerrePositivity.KST.SConstruction.assemblyArrowSource

#check @SerrePositivity.KST.SConstruction.assemblyArrowTarget
#print axioms SerrePositivity.KST.SConstruction.assemblyArrowTarget

#check @SerrePositivity.KST.SConstruction.assemblyArrowHom
#print axioms SerrePositivity.KST.SConstruction.assemblyArrowHom

#check @SerrePositivity.KST.SConstruction.assemblyArrowPre
#print axioms SerrePositivity.KST.SConstruction.assemblyArrowPre

#check @SerrePositivity.KST.SConstruction.assemblyArrowPost
#print axioms SerrePositivity.KST.SConstruction.assemblyArrowPost

#check @SerrePositivity.KST.SConstruction.assemblyArrow_comm
#print axioms SerrePositivity.KST.SConstruction.assemblyArrow_comm

#check @SerrePositivity.KST.SConstruction.assemblyArrowMk
#print axioms SerrePositivity.KST.SConstruction.assemblyArrowMk

#check @SerrePositivity.KST.SConstruction.assemblyArrowMap
#print axioms SerrePositivity.KST.SConstruction.assemblyArrowMap

#check @SerrePositivity.KST.SConstruction.assemblyArrowPre_id
#print axioms SerrePositivity.KST.SConstruction.assemblyArrowPre_id

#check @SerrePositivity.KST.SConstruction.assemblyArrowPost_id
#print axioms SerrePositivity.KST.SConstruction.assemblyArrowPost_id

#check @SerrePositivity.KST.SConstruction.assemblyArrowPre_comp
#print axioms SerrePositivity.KST.SConstruction.assemblyArrowPre_comp

#check @SerrePositivity.KST.SConstruction.assemblyArrowPost_comp
#print axioms SerrePositivity.KST.SConstruction.assemblyArrowPost_comp

#check @SerrePositivity.KST.SConstruction.pointedExtensionArrowSpace
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionArrowSpace

#check @SerrePositivity.KST.SConstruction.pointedExtensionArrow_restriction
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionArrow_restriction

#check @SerrePositivity.KST.SConstruction.pointedExtensionArrowMap
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionArrowMap

#check @SerrePositivity.KST.SConstruction.pointedExtensionArrowMap_id
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionArrowMap_id

#check @SerrePositivity.KST.SConstruction.pointedExtensionArrowMap_comp
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionArrowMap_comp

#check @SerrePositivity.KST.SConstruction.pointedExtensionArrowDiagram
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionArrowDiagram

#check @SerrePositivity.KST.SConstruction.pointedExtensionArrowSpace_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionArrowSpace_isContractibleKan

#check @SerrePositivity.KST.SConstruction.pointedLiftArrowSpace
#print axioms SerrePositivity.KST.SConstruction.pointedLiftArrowSpace

#check @SerrePositivity.KST.SConstruction.pointedLiftArrow_base
#print axioms SerrePositivity.KST.SConstruction.pointedLiftArrow_base

#check @SerrePositivity.KST.SConstruction.pointedLiftArrowMap
#print axioms SerrePositivity.KST.SConstruction.pointedLiftArrowMap

#check @SerrePositivity.KST.SConstruction.pointedLiftArrowMap_id
#print axioms SerrePositivity.KST.SConstruction.pointedLiftArrowMap_id

#check @SerrePositivity.KST.SConstruction.pointedLiftArrowMap_comp
#print axioms SerrePositivity.KST.SConstruction.pointedLiftArrowMap_comp

#check @SerrePositivity.KST.SConstruction.pointedLiftArrowDiagram
#print axioms SerrePositivity.KST.SConstruction.pointedLiftArrowDiagram

#check @SerrePositivity.KST.SConstruction.pointedLiftArrowSpace_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.pointedLiftArrowSpace_isContractibleKan

#check @SerrePositivity.KST.SConstruction.selectionTerminalDiagram
#print axioms SerrePositivity.KST.SConstruction.selectionTerminalDiagram

#check @SerrePositivity.KST.SConstruction.selectionTerminalMap
#print axioms SerrePositivity.KST.SConstruction.selectionTerminalMap

#check @SerrePositivity.KST.SConstruction.selectionTerminalSections_isTerminal
#print axioms SerrePositivity.KST.SConstruction.selectionTerminalSections_isTerminal

#check @SerrePositivity.KST.SConstruction.contractibleDiagramSelections_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.contractibleDiagramSelections_isContractibleKan

#check @SerrePositivity.KST.SConstruction.diagramSelectionAt
#print axioms SerrePositivity.KST.SConstruction.diagramSelectionAt

#check @SerrePositivity.KST.SConstruction.contractibleDiagramSelections_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.contractibleDiagramSelections_relative_lifting

#check @SerrePositivity.KST.SConstruction.selectionTerminalWeightedProjection_isIso
#print axioms SerrePositivity.KST.SConstruction.selectionTerminalWeightedProjection_isIso

#check @SerrePositivity.KST.SConstruction.contractibleWeightedDiagramProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.contractibleWeightedDiagramProjection_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.contractibleWeightedDiagram_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.contractibleWeightedDiagram_relative_lifting

#check @SerrePositivity.KST.SConstruction.contractibleWeightedDiagram_section_extension
#print axioms SerrePositivity.KST.SConstruction.contractibleWeightedDiagram_section_extension

#check @SerrePositivity.KST.SConstruction.oneDirectionKanUnitNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanUnitNat

#check @SerrePositivity.KST.SConstruction.oneDirectionMappingPathProjectionNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionMappingPathProjectionNat

#check @SerrePositivity.KST.SConstruction.oneDirectionMappingPathRetractionNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionMappingPathRetractionNat

#check @SerrePositivity.KST.SConstruction.kanAssemblyInputArrowDiagram
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyInputArrowDiagram

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseInputArrowDiagram
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseInputArrowDiagram

#check @SerrePositivity.KST.SConstruction.kanAssemblyInputArrowDiagram_obj
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyInputArrowDiagram_obj

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseInputArrowDiagram_obj
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseInputArrowDiagram_obj

#check @SerrePositivity.KST.SConstruction.kanAssemblyInputArrowDiagram_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyInputArrowDiagram_isContractibleKan

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseInputArrowDiagram_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseInputArrowDiagram_isContractibleKan

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentChoices
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentChoices

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentChoices
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentChoices

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentChoices_isContractibleKan

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentChoices_isContractibleKan

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentFamily
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentFamily

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentFamily
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentFamily

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentChoices_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentChoices_relative_lifting

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentChoices_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentChoices_relative_lifting

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentSection_extension
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentSection_extension

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentSection_extension
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentSection_extension

#check @SerrePositivity.KST.SConstruction.pointedMappingArrowDiagram
#print axioms SerrePositivity.KST.SConstruction.pointedMappingArrowDiagram

#check @SerrePositivity.KST.SConstruction.pointedExtensionArrowEvaluation
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionArrowEvaluation

#check @SerrePositivity.KST.SConstruction.pointedLiftArrowEvaluation
#print axioms SerrePositivity.KST.SConstruction.pointedLiftArrowEvaluation

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentEvaluation
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentEvaluation

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentEvaluation
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentEvaluation

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentEvaluation_app
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentEvaluation_app

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentEvaluation_app
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentEvaluation_app

#check @SerrePositivity.KST.SConstruction.pointedExtensionBaseIso
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionBaseIso

#check @SerrePositivity.KST.SConstruction.pointedExtensionBaseIso_projection
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionBaseIso_projection

#check @SerrePositivity.KST.SConstruction.pointedExtensionBaseIso_map
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionBaseIso_map

#check @SerrePositivity.KST.SConstruction.pointedLiftBaseIso
#print axioms SerrePositivity.KST.SConstruction.pointedLiftBaseIso

#check @SerrePositivity.KST.SConstruction.pointedLiftBaseIso_projection
#print axioms SerrePositivity.KST.SConstruction.pointedLiftBaseIso_projection

#check @SerrePositivity.KST.SConstruction.pointedLiftBaseIso_map
#print axioms SerrePositivity.KST.SConstruction.pointedLiftBaseIso_map

#check @SerrePositivity.KST.SConstruction.pointedLiftBaseIso_evaluation
#print axioms SerrePositivity.KST.SConstruction.pointedLiftBaseIso_evaluation

#check @SerrePositivity.KST.SConstruction.pointedLiftBaseIso_map_post
#print axioms SerrePositivity.KST.SConstruction.pointedLiftBaseIso_map_post

#check @SerrePositivity.KST.SConstruction.kanAssemblyInputIdentity_constraint
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyInputIdentity_constraint

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseInputIdentity_constraint
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseInputIdentity_constraint

#check @SerrePositivity.KST.SConstruction.kanAssemblyInputIdentityChoicesIso
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyInputIdentityChoicesIso

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseInputIdentityChoicesIso
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseInputIdentityChoicesIso

#check @SerrePositivity.KST.SConstruction.kanAssemblyInputIdentityChoicesIso_family
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyInputIdentityChoicesIso_family

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseInputIdentityChoicesIso_family
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseInputIdentityChoicesIso_family

#check @SerrePositivity.KST.SConstruction.kanAssemblyInputIdentityChoicesIso_map
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyInputIdentityChoicesIso_map

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseInputIdentityChoicesIso_map
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseInputIdentityChoicesIso_map

#check @SerrePositivity.KST.SConstruction.diagramSelectionVertex
#print axioms SerrePositivity.KST.SConstruction.diagramSelectionVertex

#check @SerrePositivity.KST.SConstruction.bousfieldKanWeight_identity_vertex
#print axioms SerrePositivity.KST.SConstruction.bousfieldKanWeight_identity_vertex

#check @SerrePositivity.KST.SConstruction.diagramSelectionVertex_transport
#print axioms SerrePositivity.KST.SConstruction.diagramSelectionVertex_transport

#check @SerrePositivity.KST.SConstruction.diagramSelectionOverArrow
#print axioms SerrePositivity.KST.SConstruction.diagramSelectionOverArrow

#check @SerrePositivity.KST.SConstruction.diagramSelectionEdge
#print axioms SerrePositivity.KST.SConstruction.diagramSelectionEdge

#check @SerrePositivity.KST.SConstruction.diagramSelectionEdge_edge
#print axioms SerrePositivity.KST.SConstruction.diagramSelectionEdge_edge

#check @SerrePositivity.KST.SConstruction.diagramSelectionTransportEdge
#print axioms SerrePositivity.KST.SConstruction.diagramSelectionTransportEdge

#check @SerrePositivity.KST.SConstruction.assemblyArrowFromSource
#print axioms SerrePositivity.KST.SConstruction.assemblyArrowFromSource

#check @SerrePositivity.KST.SConstruction.assemblyArrowFromTarget
#print axioms SerrePositivity.KST.SConstruction.assemblyArrowFromTarget

#check @SerrePositivity.KST.SConstruction.assemblyArrowFromSource_pre
#print axioms SerrePositivity.KST.SConstruction.assemblyArrowFromSource_pre

#check @SerrePositivity.KST.SConstruction.assemblyArrowFromSource_post
#print axioms SerrePositivity.KST.SConstruction.assemblyArrowFromSource_post

#check @SerrePositivity.KST.SConstruction.assemblyArrowFromTarget_pre
#print axioms SerrePositivity.KST.SConstruction.assemblyArrowFromTarget_pre

#check @SerrePositivity.KST.SConstruction.assemblyArrowFromTarget_post
#print axioms SerrePositivity.KST.SConstruction.assemblyArrowFromTarget_post

#check @SerrePositivity.KST.SConstruction.pointedExtensionArrowIdentityIso
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionArrowIdentityIso

#check @SerrePositivity.KST.SConstruction.pointedExtensionSourceTransport
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionSourceTransport

#check @SerrePositivity.KST.SConstruction.pointedExtensionTargetTransport
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionTargetTransport

#check @SerrePositivity.KST.SConstruction.pointedExtensionArrowIdentityIso_source
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionArrowIdentityIso_source

#check @SerrePositivity.KST.SConstruction.pointedExtensionArrowIdentityIso_target
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionArrowIdentityIso_target

#check @SerrePositivity.KST.SConstruction.pointedLiftArrowIdentityIso
#print axioms SerrePositivity.KST.SConstruction.pointedLiftArrowIdentityIso

#check @SerrePositivity.KST.SConstruction.pointedLiftSourceTransport
#print axioms SerrePositivity.KST.SConstruction.pointedLiftSourceTransport

#check @SerrePositivity.KST.SConstruction.pointedLiftTargetTransport
#print axioms SerrePositivity.KST.SConstruction.pointedLiftTargetTransport

#check @SerrePositivity.KST.SConstruction.pointedLiftArrowIdentityIso_source
#print axioms SerrePositivity.KST.SConstruction.pointedLiftArrowIdentityIso_source

#check @SerrePositivity.KST.SConstruction.pointedLiftArrowIdentityIso_target
#print axioms SerrePositivity.KST.SConstruction.pointedLiftArrowIdentityIso_target

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentChoiceAt
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentChoiceAt

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentChoiceAt
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentChoiceAt

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyCoherentChoiceAt
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyCoherentChoiceAt

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyCoherentAdjointAt
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyCoherentAdjointAt

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyCoherentAdjointAt_component
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyCoherentAdjointAt_component

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyCoherentAdjointAt_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyCoherentAdjointAt_piIsomorphism

#check @SerrePositivity.KST.SConstruction.kanAssemblyInputIdentityChoicesIso_source
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyInputIdentityChoicesIso_source

#check @SerrePositivity.KST.SConstruction.kanAssemblyInputIdentityChoicesIso_target
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyInputIdentityChoicesIso_target

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseInputIdentityChoicesIso_source
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseInputIdentityChoicesIso_source

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseInputIdentityChoicesIso_target
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseInputIdentityChoicesIso_target

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentSourceEdge
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentSourceEdge

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentTargetEdge
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentTargetEdge

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentSourceEdge
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentSourceEdge

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentTargetEdge
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentTargetEdge

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentLegTriangle_nonempty
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentLegTriangle_nonempty

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentLegTriangle_nonempty
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentLegTriangle_nonempty

#check @SerrePositivity.KST.SConstruction.bousfieldKanWeight_overArrow_edge
#print axioms SerrePositivity.KST.SConstruction.bousfieldKanWeight_overArrow_edge

#check @SerrePositivity.KST.SConstruction.diagramSelectionCompositionFirstEdge
#print axioms SerrePositivity.KST.SConstruction.diagramSelectionCompositionFirstEdge

#check @SerrePositivity.KST.SConstruction.diagramSelectionCompositionTriangle_nonempty
#print axioms SerrePositivity.KST.SConstruction.diagramSelectionCompositionTriangle_nonempty

#check @SerrePositivity.KST.SConstruction.diagramSelectionTransportEdge_edge
#print axioms SerrePositivity.KST.SConstruction.diagramSelectionTransportEdge_edge

#check @SerrePositivity.KST.SConstruction.kanCospanHorn
#print axioms SerrePositivity.KST.SConstruction.kanCospanHorn

#check @SerrePositivity.KST.SConstruction.kanCospanHorn_source
#print axioms SerrePositivity.KST.SConstruction.kanCospanHorn_source

#check @SerrePositivity.KST.SConstruction.kanCospanHorn_target
#print axioms SerrePositivity.KST.SConstruction.kanCospanHorn_target

#check @SerrePositivity.KST.SConstruction.kanCospanPastingChoices
#print axioms SerrePositivity.KST.SConstruction.kanCospanPastingChoices

#check @SerrePositivity.KST.SConstruction.kanCospanPastingChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.kanCospanPastingChoices_isContractibleKan

#check @SerrePositivity.KST.SConstruction.kanCospanPastingChoices_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.kanCospanPastingChoices_relative_lifting

#check @SerrePositivity.KST.SConstruction.kanCospanPastingAt
#print axioms SerrePositivity.KST.SConstruction.kanCospanPastingAt

#check @SerrePositivity.KST.SConstruction.kanCospanPastingAt_source
#print axioms SerrePositivity.KST.SConstruction.kanCospanPastingAt_source

#check @SerrePositivity.KST.SConstruction.kanCospanPastingAt_target
#print axioms SerrePositivity.KST.SConstruction.kanCospanPastingAt_target

#check @SerrePositivity.KST.SConstruction.kanCospanPastedEdge
#print axioms SerrePositivity.KST.SConstruction.kanCospanPastedEdge

#check @SerrePositivity.KST.SConstruction.kanCospanPastedTriangle
#print axioms SerrePositivity.KST.SConstruction.kanCospanPastedTriangle

#check @SerrePositivity.KST.SConstruction.diagramFamilyTranspose
#print axioms SerrePositivity.KST.SConstruction.diagramFamilyTranspose

#check @SerrePositivity.KST.SConstruction.diagramUniversalFamily
#print axioms SerrePositivity.KST.SConstruction.diagramUniversalFamily

#check @SerrePositivity.KST.SConstruction.diagramUniversalFamily_evaluation
#print axioms SerrePositivity.KST.SConstruction.diagramUniversalFamily_evaluation

#check @SerrePositivity.KST.SConstruction.diagramUniversalFamily_edge_evaluation
#print axioms SerrePositivity.KST.SConstruction.diagramUniversalFamily_edge_evaluation

#check @SerrePositivity.KST.SConstruction.diagramUniversalFamily_transportEdge_evaluation
#print axioms SerrePositivity.KST.SConstruction.diagramUniversalFamily_transportEdge_evaluation

#check @SerrePositivity.KST.SConstruction.diagramFamilyCospanPastingChoices
#print axioms SerrePositivity.KST.SConstruction.diagramFamilyCospanPastingChoices

#check @SerrePositivity.KST.SConstruction.diagramFamilyCospanPastingChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.diagramFamilyCospanPastingChoices_isContractibleKan

#check @SerrePositivity.KST.SConstruction.diagramUniversalCospanPastingChoices
#print axioms SerrePositivity.KST.SConstruction.diagramUniversalCospanPastingChoices

#check @SerrePositivity.KST.SConstruction.diagramUniversalCospanPastingChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.diagramUniversalCospanPastingChoices_isContractibleKan

#check @SerrePositivity.KST.SConstruction.diagramUniversalCospanPastingFamily
#print axioms SerrePositivity.KST.SConstruction.diagramUniversalCospanPastingFamily

#check @SerrePositivity.KST.SConstruction.diagramUniversalCospanPastingFamily_source
#print axioms SerrePositivity.KST.SConstruction.diagramUniversalCospanPastingFamily_source

#check @SerrePositivity.KST.SConstruction.diagramUniversalCospanPastingFamily_target
#print axioms SerrePositivity.KST.SConstruction.diagramUniversalCospanPastingFamily_target

#check @SerrePositivity.KST.SConstruction.diagramUniversalCospanPastedEdge
#print axioms SerrePositivity.KST.SConstruction.diagramUniversalCospanPastedEdge

#check @SerrePositivity.KST.SConstruction.diagramUniversalCospanPastedTriangle
#print axioms SerrePositivity.KST.SConstruction.diagramUniversalCospanPastedTriangle

#check @SerrePositivity.KST.SConstruction.diagramUniversalCospanPastingChoices_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.diagramUniversalCospanPastingChoices_relative_lifting

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentPastingChoices
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentPastingChoices

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentPastingChoices
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentPastingChoices

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentPastingChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentPastingChoices_isContractibleKan

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentPastingChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentPastingChoices_isContractibleKan

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentPastingFamily
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentPastingFamily

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentPastingFamily
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentPastingFamily

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentPastingChoices_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentPastingChoices_relative_lifting

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentPastingChoices_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentPastingChoices_relative_lifting

#check @SerrePositivity.KST.SConstruction.kanCospanPastedTriangle_map
#print axioms SerrePositivity.KST.SConstruction.kanCospanPastedTriangle_map

#check @SerrePositivity.KST.SConstruction.diagramUniversalCospanPastedTriangle_evaluation
#print axioms SerrePositivity.KST.SConstruction.diagramUniversalCospanPastedTriangle_evaluation

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentPastedEdge
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentPastedEdge

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentPastedTriangle
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentPastedTriangle

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentPastedEdge
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentPastedEdge

#check @SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentPastedTriangle
#print axioms SerrePositivity.KST.SConstruction.oneDirectionInverseCoherentPastedTriangle

#check @SerrePositivity.KST.SConstruction.pointedKanProperty
#print axioms SerrePositivity.KST.SConstruction.pointedKanProperty

#check @SerrePositivity.KST.SConstruction.PointedKanObject
#print axioms SerrePositivity.KST.SConstruction.PointedKanObject

#check @SerrePositivity.KST.SConstruction.pointedKanObject_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.pointedKanObject_simplicialCategory

#check @SerrePositivity.KST.SConstruction.pointedKanObject_kanComplex
#print axioms SerrePositivity.KST.SConstruction.pointedKanObject_kanComplex

#check @SerrePositivity.KST.SConstruction.pointedKanObject_hom_eq
#print axioms SerrePositivity.KST.SConstruction.pointedKanObject_hom_eq

#check @SerrePositivity.KST.SConstruction.pointedKanObject_sHom_kanComplex
#print axioms SerrePositivity.KST.SConstruction.pointedKanObject_sHom_kanComplex

#check @SerrePositivity.KST.SConstruction.PointedKanInfinity
#print axioms SerrePositivity.KST.SConstruction.PointedKanInfinity

#check @SerrePositivity.KST.SConstruction.pointedKanInfinity_quasicategory
#print axioms SerrePositivity.KST.SConstruction.pointedKanInfinity_quasicategory

#check @SerrePositivity.KST.SConstruction.pointedKanDiagram
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagram

#check @SerrePositivity.KST.SConstruction.pointedKanDiagram_forget
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagram_forget

#check @SerrePositivity.KST.SConstruction.pointedKanCoherentDiagram
#print axioms SerrePositivity.KST.SConstruction.pointedKanCoherentDiagram

#check @SerrePositivity.KST.SConstruction.pointedKanReplacementObjectFunctor
#print axioms SerrePositivity.KST.SConstruction.pointedKanReplacementObjectFunctor

#check @SerrePositivity.KST.SConstruction.pointedKanObject_vertex_eq
#print axioms SerrePositivity.KST.SConstruction.pointedKanObject_vertex_eq

#check @SerrePositivity.KST.SConstruction.pointedKanObject_nonempty_vertexIso_of_component
#print axioms SerrePositivity.KST.SConstruction.pointedKanObject_nonempty_vertexIso_of_component

#check @SerrePositivity.KST.SConstruction.pointedKanObject_edge_isInvertible_of_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.pointedKanObject_edge_isInvertible_of_piIsomorphism

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramNatTrans
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramNatTrans

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramHomotopy
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramHomotopy

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramFunctorIso
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramFunctorIso

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramInverseHomotopy
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramInverseHomotopy

#check @SerrePositivity.KST.SConstruction.oneDirectionPointedKanDiagram
#print axioms SerrePositivity.KST.SConstruction.oneDirectionPointedKanDiagram

#check @SerrePositivity.KST.SConstruction.boundaryPointedKanDiagram
#print axioms SerrePositivity.KST.SConstruction.boundaryPointedKanDiagram

#check @SerrePositivity.KST.SConstruction.oneDirectionCoherentComparisonIso
#print axioms SerrePositivity.KST.SConstruction.oneDirectionCoherentComparisonIso

#check @SerrePositivity.KST.SConstruction.oneDirectionCoherentInverseHomotopy
#print axioms SerrePositivity.KST.SConstruction.oneDirectionCoherentInverseHomotopy

#check @SerrePositivity.KST.SConstruction.pointedDiagramReplacement_isKan
#print axioms SerrePositivity.KST.SConstruction.pointedDiagramReplacement_isKan

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramUnitIso
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramUnitIso

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramUnitInverseHomotopy
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramUnitInverseHomotopy

#check @SerrePositivity.KST.SConstruction.pointedKanReplacedNatTransHomotopy
#print axioms SerrePositivity.KST.SConstruction.pointedKanReplacedNatTransHomotopy

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramExtensionHomotopy
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramExtensionHomotopy

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramExtensionTriangle
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramExtensionTriangle

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentDiagramHomotopy
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentDiagramHomotopy

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentDiagramTriangle
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentDiagramTriangle

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramHomotopy
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramHomotopy

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramTriangle
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramTriangle

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramHomotopyEdgeAt
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramHomotopyEdgeAt

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramHomotopyMapAt
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramHomotopyMapAt

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramHomotopyMapAt_edge
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramHomotopyMapAt_edge

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramHomotopyMapAt_natTrans
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramHomotopyMapAt_natTrans

#check @SerrePositivity.KST.SConstruction.oneDirectionCoherentInverseDiagramMapAt
#print axioms SerrePositivity.KST.SConstruction.oneDirectionCoherentInverseDiagramMapAt

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentDiagramMapAt
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentDiagramMapAt

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramMapAt
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramMapAt

#check @SerrePositivity.KST.SConstruction.piZero_ulift_reflect
#print axioms SerrePositivity.KST.SConstruction.piZero_ulift_reflect

#check @SerrePositivity.KST.SConstruction.pointedKanHomotopyClass
#print axioms SerrePositivity.KST.SConstruction.pointedKanHomotopyClass

#check @SerrePositivity.KST.SConstruction.pointedKanHomotopyClass_comparison
#print axioms SerrePositivity.KST.SConstruction.pointedKanHomotopyClass_comparison

#check @SerrePositivity.KST.SConstruction.pointedKanHomotopyClass_eq_iff
#print axioms SerrePositivity.KST.SConstruction.pointedKanHomotopyClass_eq_iff

#check @SerrePositivity.KST.SConstruction.pointedKanHomotopyClass_id
#print axioms SerrePositivity.KST.SConstruction.pointedKanHomotopyClass_id

#check @SerrePositivity.KST.SConstruction.pointedKanHomotopyClass_comp
#print axioms SerrePositivity.KST.SConstruction.pointedKanHomotopyClass_comp

#check @SerrePositivity.KST.SConstruction.pointedKanObject_component_comp_of_triangle
#print axioms SerrePositivity.KST.SConstruction.pointedKanObject_component_comp_of_triangle

#check @SerrePositivity.KST.SConstruction.pointedKanUnderlying_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.pointedKanUnderlying_simplicialCategory

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramHomotopyMapAt_yoneda
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramHomotopyMapAt_yoneda

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramTriangle_components
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramTriangle_components

#check @SerrePositivity.KST.SConstruction.diagramFunctorEdge_homotopy_roundtrip
#print axioms SerrePositivity.KST.SConstruction.diagramFunctorEdge_homotopy_roundtrip

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramFunctorIso_hom
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramFunctorIso_hom

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramInverseHomotopy_hom
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramInverseHomotopy_hom

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramInverse_leftTriangle_nonempty
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramInverse_leftTriangle_nonempty

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramInverse_rightTriangle_nonempty
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramInverse_rightTriangle_nonempty

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramHomotopyMapAt_refl
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramHomotopyMapAt_refl

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramInverse_left_component
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramInverse_left_component

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramInverse_right_component
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramInverse_right_component

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramUnitInverseMapAt
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramUnitInverseMapAt

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramUnitInverse_right_component
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramUnitInverse_right_component

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramExtensionMapAt
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramExtensionMapAt

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramExtension_post_unit_component
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramExtension_post_unit_component

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramExtensionMapAt_component
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramExtensionMapAt_component

#check @SerrePositivity.KST.SConstruction.oneDirectionCoherentInverseDiagramMapAt_component
#print axioms SerrePositivity.KST.SConstruction.oneDirectionCoherentInverseDiagramMapAt_component

#check @SerrePositivity.KST.SConstruction.kanAssemblyCoherentDiagramMapAt_component
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyCoherentDiagramMapAt_component

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramMapAt_factor_component
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramMapAt_factor_component

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramMapAt_component
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramMapAt_component

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramHomotopyFunctorIso
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramHomotopyFunctorIso

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramMapAt_original_component
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramMapAt_original_component

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramMapAt_original_homotopy
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramMapAt_original_homotopy

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramMapAt_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramMapAt_piIsomorphism

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramIso
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyCoherentDiagramIso

#check @SerrePositivity.KST.SConstruction.diagramPinchedVertex_map
#print axioms SerrePositivity.KST.SConstruction.diagramPinchedVertex_map

#check @SerrePositivity.KST.SConstruction.exists_fixedEndpoint_restriction_correction
#print axioms SerrePositivity.KST.SConstruction.exists_fixedEndpoint_restriction_correction

#check @SerrePositivity.KST.SConstruction.vertexDiscreteFunctionSimplex
#print axioms SerrePositivity.KST.SConstruction.vertexDiscreteFunctionSimplex

#check @SerrePositivity.KST.SConstruction.vertexDiscreteEvaluate
#print axioms SerrePositivity.KST.SConstruction.vertexDiscreteEvaluate

#check @SerrePositivity.KST.SConstruction.vertexDiscreteFunctionSimplex_evaluate
#print axioms SerrePositivity.KST.SConstruction.vertexDiscreteFunctionSimplex_evaluate

#check @SerrePositivity.KST.SConstruction.vertexDiscreteFunctionSimplex_reconstruct
#print axioms SerrePositivity.KST.SConstruction.vertexDiscreteFunctionSimplex_reconstruct

#check @SerrePositivity.KST.SConstruction.vertexDiscreteFunctionSimplex_map
#print axioms SerrePositivity.KST.SConstruction.vertexDiscreteFunctionSimplex_map

#check @SerrePositivity.KST.SConstruction.vertexDiscreteEvaluate_functorVertex
#print axioms SerrePositivity.KST.SConstruction.vertexDiscreteEvaluate_functorVertex

#check @SerrePositivity.KST.SConstruction.vertexDiscretePinchedSimplex
#print axioms SerrePositivity.KST.SConstruction.vertexDiscretePinchedSimplex

#check @SerrePositivity.KST.SConstruction.vertexDiscretePinchedSimplex_map
#print axioms SerrePositivity.KST.SConstruction.vertexDiscretePinchedSimplex_map

#check @SerrePositivity.KST.SConstruction.vertexDiscretePinchedSimplex_reconstruct
#print axioms SerrePositivity.KST.SConstruction.vertexDiscretePinchedSimplex_reconstruct

#check @SerrePositivity.KST.SConstruction.vertexDiscretePinched_nonempty_edge
#print axioms SerrePositivity.KST.SConstruction.vertexDiscretePinched_nonempty_edge

#check @SerrePositivity.KST.SConstruction.vertexDiscretePinched_piZero_injective
#print axioms SerrePositivity.KST.SConstruction.vertexDiscretePinched_piZero_injective

#check @SerrePositivity.KST.SConstruction.vertexDiscreteFunctionSimplex_vertex
#print axioms SerrePositivity.KST.SConstruction.vertexDiscreteFunctionSimplex_vertex

#check @SerrePositivity.KST.SConstruction.vertexDiscreteSpecifiedEdge
#print axioms SerrePositivity.KST.SConstruction.vertexDiscreteSpecifiedEdge

#check @SerrePositivity.KST.SConstruction.vertexDiscreteSpecifiedEdge_evaluate
#print axioms SerrePositivity.KST.SConstruction.vertexDiscreteSpecifiedEdge_evaluate

#check @SerrePositivity.KST.SConstruction.vertexDiscreteFunctorEdge_hom_ext
#print axioms SerrePositivity.KST.SConstruction.vertexDiscreteFunctorEdge_hom_ext

#check @SerrePositivity.KST.SConstruction.vertexDiscrete_restriction_edge_evaluate
#print axioms SerrePositivity.KST.SConstruction.vertexDiscrete_restriction_edge_evaluate

#check @SerrePositivity.KST.SConstruction.exists_vertexDiscrete_homotopy_correction
#print axioms SerrePositivity.KST.SConstruction.exists_vertexDiscrete_homotopy_correction

#check @SerrePositivity.KST.SConstruction.diagramEdge_homMk_ofEq_iff
#print axioms SerrePositivity.KST.SConstruction.diagramEdge_homMk_ofEq_iff

#check @SerrePositivity.KST.SConstruction.pointedKanCoherentDiagram_vertex_any
#print axioms SerrePositivity.KST.SConstruction.pointedKanCoherentDiagram_vertex_any

#check @SerrePositivity.KST.SConstruction.pointedKanCoherentDiagram_discrete_vertex
#print axioms SerrePositivity.KST.SConstruction.pointedKanCoherentDiagram_discrete_vertex

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramSpecifiedVertexEdge
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramSpecifiedVertexEdge

#check @SerrePositivity.KST.SConstruction.pointedKanDiagramSpecifiedVertexEdge_hom
#print axioms SerrePositivity.KST.SConstruction.pointedKanDiagramSpecifiedVertexEdge_hom

#check @SerrePositivity.KST.SConstruction.exists_pointedKanDiagram_specified_components
#print axioms SerrePositivity.KST.SConstruction.exists_pointedKanDiagram_specified_components

#check @SerrePositivity.KST.SConstruction.exists_boundaryAssemblySpecifiedCoherentHomotopy
#print axioms SerrePositivity.KST.SConstruction.exists_boundaryAssemblySpecifiedCoherentHomotopy

#check @SerrePositivity.KST.SConstruction.exists_boundaryAssemblyOriginalCoherentHomotopy
#print axioms SerrePositivity.KST.SConstruction.exists_boundaryAssemblyOriginalCoherentHomotopy

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalCoherentHomotopy
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalCoherentHomotopy

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalCoherentHomotopy_component
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalCoherentHomotopy_component

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalCoherentHomotopy_hom
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalCoherentHomotopy_hom

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalCoherentHomotopy_vertex_edge
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalCoherentHomotopy_vertex_edge

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalCoherentIso
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalCoherentIso

#check @SerrePositivity.KST.SConstruction.suspensionLoopMapping_curry'
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopMapping_curry'

#check @SerrePositivity.KST.SConstruction.suspensionLoopPointedMappingIso
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopPointedMappingIso

#check @SerrePositivity.KST.SConstruction.suspensionLoopMappingIso
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopMappingIso

#check @SerrePositivity.KST.SConstruction.suspensionLoopMappingIso_vertex
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopMappingIso_vertex

#check @SerrePositivity.KST.SConstruction.suspensionLoopPointedMappingIso_post
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopPointedMappingIso_post

#check @SerrePositivity.KST.SConstruction.suspensionLoopPointedMappingIso_pre
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopPointedMappingIso_pre

#check @SerrePositivity.KST.SConstruction.suspensionLoopMappingIso_post
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopMappingIso_post

#check @SerrePositivity.KST.SConstruction.suspensionLoopMappingIso_pre
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopMappingIso_pre

#check @SerrePositivity.KST.SConstruction.suspensionLoopMappingIso_inv_vertex
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopMappingIso_inv_vertex

#check @SerrePositivity.KST.SConstruction.suspensionLoopMappingIso_inv_post
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopMappingIso_inv_post

#check @SerrePositivity.KST.SConstruction.suspensionLoopMappingIso_inv_pre
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopMappingIso_inv_pre

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblySigmaAt
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblySigmaAt

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblySigmaFamily
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblySigmaFamily

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblySigmaFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblySigmaFamily_vertex

#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblySigmaAt_component
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblySigmaAt_component

#check @SerrePositivity.KST.SConstruction.boundaryAssemblySuspensionCylinderFamily
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblySuspensionCylinderFamily

#check @SerrePositivity.KST.SConstruction.boundaryAssemblySuspensionCylinderFamily_source
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblySuspensionCylinderFamily_source

#check @SerrePositivity.KST.SConstruction.boundaryAssemblySuspensionCylinderFamily_target
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblySuspensionCylinderFamily_target

#check @SerrePositivity.KST.SConstruction.pointedMappingIhom_eq_basedHomFunctor
#print axioms SerrePositivity.KST.SConstruction.pointedMappingIhom_eq_basedHomFunctor

#check @SerrePositivity.KST.SConstruction.suspensionLoopMappingFamily_pre
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopMappingFamily_pre

#check @SerrePositivity.KST.SConstruction.suspensionLoopMappingFamily_prePointed
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopMappingFamily_prePointed

#check @SerrePositivity.KST.SConstruction.suspensionLoopPointedMappingIso_inv_enriched_pre

#print axioms SerrePositivity.KST.SConstruction.suspensionLoopPointedMappingIso_inv_enriched_pre


#check @SerrePositivity.KST.SConstruction.suspensionLoopPointedMappingIso_enriched_pre

#print axioms SerrePositivity.KST.SConstruction.suspensionLoopPointedMappingIso_enriched_pre


#check @SerrePositivity.KST.SConstruction.suspensionLoopMappingIso_inv_enriched_pre

#print axioms SerrePositivity.KST.SConstruction.suspensionLoopMappingIso_inv_enriched_pre


#check @SerrePositivity.KST.SConstruction.suspensionLoopMappingFamilies_inv_pre
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopMappingFamilies_inv_pre

#check @SerrePositivity.KST.SConstruction.pointedLoopHom
#print axioms SerrePositivity.KST.SConstruction.pointedLoopHom

#check @SerrePositivity.KST.SConstruction.pointedLoopHom_evaluation
#print axioms SerrePositivity.KST.SConstruction.pointedLoopHom_evaluation

#check @SerrePositivity.KST.SConstruction.pointedLoopHom_curry'
#print axioms SerrePositivity.KST.SConstruction.pointedLoopHom_curry'

#check @SerrePositivity.KST.SConstruction.pointedLoopHom_id
#print axioms SerrePositivity.KST.SConstruction.pointedLoopHom_id

#check @SerrePositivity.KST.SConstruction.pointedLoopHom_comp
#print axioms SerrePositivity.KST.SConstruction.pointedLoopHom_comp

#check @SerrePositivity.KST.SConstruction.pointedLoopHom_vertex
#print axioms SerrePositivity.KST.SConstruction.pointedLoopHom_vertex

#check @SerrePositivity.KST.SConstruction.pointedLoopUnderlying_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.pointedLoopUnderlying_simplicialCategory

#check @SerrePositivity.KST.SConstruction.pointedLoopHom_simplicial_comp
#print axioms SerrePositivity.KST.SConstruction.pointedLoopHom_simplicial_comp

#check @SerrePositivity.KST.SConstruction.pointedLoopHom_simplicial_id
#print axioms SerrePositivity.KST.SConstruction.pointedLoopHom_simplicial_id

#check @SerrePositivity.KST.SConstruction.pointedLoopEnrichedFunctor
#print axioms SerrePositivity.KST.SConstruction.pointedLoopEnrichedFunctor

#check @SerrePositivity.KST.SConstruction.pointedKanLoopObject
#print axioms SerrePositivity.KST.SConstruction.pointedKanLoopObject

#check @SerrePositivity.KST.SConstruction.pointedKanLoopEnrichedFunctor
#print axioms SerrePositivity.KST.SConstruction.pointedKanLoopEnrichedFunctor

#check @SerrePositivity.KST.SConstruction.pointedKanLoopFunctor
#print axioms SerrePositivity.KST.SConstruction.pointedKanLoopFunctor

#check @SerrePositivity.KST.SConstruction.pointedKanLoopFunctor_map_hom
#print axioms SerrePositivity.KST.SConstruction.pointedKanLoopFunctor_map_hom

#check @SerrePositivity.KST.SConstruction.pointedKanLoopInfinity
#print axioms SerrePositivity.KST.SConstruction.pointedKanLoopInfinity

#check @SerrePositivity.KST.SConstruction.pointedKanLoopInfinity_vertex
#print axioms SerrePositivity.KST.SConstruction.pointedKanLoopInfinity_vertex

#check @SerrePositivity.KST.SConstruction.pointedKanLoopDiagram_eq
#print axioms SerrePositivity.KST.SConstruction.pointedKanLoopDiagram_eq

#check @SerrePositivity.KST.SConstruction.pointedKanLoopInfinity_diagram
#print axioms SerrePositivity.KST.SConstruction.pointedKanLoopInfinity_diagram

#check @SerrePositivity.KST.SConstruction.boundaryKanLoopInfinity_diagram
#print axioms SerrePositivity.KST.SConstruction.boundaryKanLoopInfinity_diagram

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNativeOmegaHomotopy
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNativeOmegaHomotopy

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNativeOmegaHomotopy_h
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNativeOmegaHomotopy_h

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNativeOmegaHomotopy_vertex_edge
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNativeOmegaHomotopy_vertex_edge

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyNativeOmegaIso
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyNativeOmegaIso

#check @SerrePositivity.KST.SConstruction.kKanSequenceLevelFunctor
#print axioms SerrePositivity.KST.SConstruction.kKanSequenceLevelFunctor

#check @SerrePositivity.KST.SConstruction.kKanSequenceLevelFunctor_obj
#print axioms SerrePositivity.KST.SConstruction.kKanSequenceLevelFunctor_obj

#check @SerrePositivity.KST.SConstruction.kKanSequenceLevelFunctor_map
#print axioms SerrePositivity.KST.SConstruction.kKanSequenceLevelFunctor_map

#check @SerrePositivity.KST.SConstruction.kKanSequenceLevelFunctor_kanComplex
#print axioms SerrePositivity.KST.SConstruction.kKanSequenceLevelFunctor_kanComplex

#check @SerrePositivity.KST.SConstruction.kKanCoherentLevelDiagram
#print axioms SerrePositivity.KST.SConstruction.kKanCoherentLevelDiagram

#check @SerrePositivity.KST.SConstruction.kKanCoherentLevelDiagram_succ
#print axioms SerrePositivity.KST.SConstruction.kKanCoherentLevelDiagram_succ

#check @SerrePositivity.KST.SConstruction.kKanCoherentLevelDiagram_zero
#print axioms SerrePositivity.KST.SConstruction.kKanCoherentLevelDiagram_zero

#check @SerrePositivity.KST.SConstruction.kKanNativeOmegaIso
#print axioms SerrePositivity.KST.SConstruction.kKanNativeOmegaIso

#check @SerrePositivity.KST.SConstruction.kKanNativeOmegaIso_succ
#print axioms SerrePositivity.KST.SConstruction.kKanNativeOmegaIso_succ

#check @SerrePositivity.KST.SConstruction.suspensionLoopPointedMappingIso_inv_factor
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopPointedMappingIso_inv_factor

#check @SerrePositivity.KST.SConstruction.pointedLoopHom_uncurry
#print axioms SerrePositivity.KST.SConstruction.pointedLoopHom_uncurry

#check @SerrePositivity.KST.SConstruction.suspensionLoopPointedMappingIso_inv_enriched_post
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopPointedMappingIso_inv_enriched_post

#check @SerrePositivity.KST.SConstruction.suspensionLoopPointedMappingIso_enriched_post
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopPointedMappingIso_enriched_post

#check @SerrePositivity.KST.SConstruction.suspensionLoopMappingIso_inv_enriched_post
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopMappingIso_inv_enriched_post

#check @SerrePositivity.KST.SConstruction.suspensionLoopMappingFamilies_inv_post
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopMappingFamilies_inv_post

#check @SerrePositivity.KST.SConstruction.enrichedCollageEmpty
#print axioms SerrePositivity.KST.SConstruction.enrichedCollageEmpty

#check @SerrePositivity.KST.SConstruction.enrichedCollageEmpty_isEmpty
#print axioms SerrePositivity.KST.SConstruction.enrichedCollageEmpty_isEmpty

#check @SerrePositivity.KST.SConstruction.enrichedCollageEmptyMap
#print axioms SerrePositivity.KST.SConstruction.enrichedCollageEmptyMap

#check @SerrePositivity.KST.SConstruction.enrichedCollageEmpty_kanComplex
#print axioms SerrePositivity.KST.SConstruction.enrichedCollageEmpty_kanComplex

#check @SerrePositivity.KST.SConstruction.EnrichedFunctorCollage
#print axioms SerrePositivity.KST.SConstruction.EnrichedFunctorCollage

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageHom
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageHom

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageId
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageId

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageComp
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageComp

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollage_id_comp
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollage_id_comp

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollage_comp_id
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollage_comp_id

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollage_assoc
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollage_assoc

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollage_enrichedCategory
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollage_enrichedCategory

#check @SerrePositivity.KST.SConstruction.EnrichedFunctorCollageCategory
#print axioms SerrePositivity.KST.SConstruction.EnrichedFunctorCollageCategory

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollage_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollage_simplicialCategory

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollage_sHom_kanComplex
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollage_sHom_kanComplex

#check @SerrePositivity.KST.SConstruction.EnrichedFunctorCollageInfinity
#print axioms SerrePositivity.KST.SConstruction.EnrichedFunctorCollageInfinity

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageInfinity_quasicategory
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageInfinity_quasicategory

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageBottom
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageBottom

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageTop
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageTop

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageProjectionObj
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageProjectionObj

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageProjectionMap
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageProjectionMap

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageProjection
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageProjection

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageBottom_projection
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageBottom_projection

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageTop_projection
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageTop_projection

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageBottomInfinity
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageBottomInfinity

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageTopInfinity
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageTopInfinity

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageProjectionInfinity
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageProjectionInfinity

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageBottomInfinity_projection
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageBottomInfinity_projection

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageTopInfinity_projection
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageTopInfinity_projection

#check @SerrePositivity.KST.SConstruction.loopCollageEvaluation_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.loopCollageEvaluation_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.pointedKanInclusionEnriched
#print axioms SerrePositivity.KST.SConstruction.pointedKanInclusionEnriched

#check @SerrePositivity.KST.SConstruction.loopCollageEvaluationObj
#print axioms SerrePositivity.KST.SConstruction.loopCollageEvaluationObj

#check @SerrePositivity.KST.SConstruction.loopCollageEvaluationMap
#print axioms SerrePositivity.KST.SConstruction.loopCollageEvaluationMap

#check @SerrePositivity.KST.SConstruction.loopCollageEvaluation
#print axioms SerrePositivity.KST.SConstruction.loopCollageEvaluation

#check @SerrePositivity.KST.SConstruction.loopCollageEvaluation_bottom
#print axioms SerrePositivity.KST.SConstruction.loopCollageEvaluation_bottom

#check @SerrePositivity.KST.SConstruction.loopCollageEvaluation_top
#print axioms SerrePositivity.KST.SConstruction.loopCollageEvaluation_top

#check @SerrePositivity.KST.SConstruction.loopCollageEvaluationNerve
#print axioms SerrePositivity.KST.SConstruction.loopCollageEvaluationNerve

#check @SerrePositivity.KST.SConstruction.loopCollageEvaluationNerve_bottom
#print axioms SerrePositivity.KST.SConstruction.loopCollageEvaluationNerve_bottom

#check @SerrePositivity.KST.SConstruction.loopCollageEvaluationNerve_top
#print axioms SerrePositivity.KST.SConstruction.loopCollageEvaluationNerve_top

#check @SerrePositivity.KST.SConstruction.loopCollageCrossMap
#print axioms SerrePositivity.KST.SConstruction.loopCollageCrossMap

#check @SerrePositivity.KST.SConstruction.loopCollageCrossMap_vertex
#print axioms SerrePositivity.KST.SConstruction.loopCollageCrossMap_vertex

#check @SerrePositivity.KST.SConstruction.loopCollageCrossMap_projection
#print axioms SerrePositivity.KST.SConstruction.loopCollageCrossMap_projection

#check @SerrePositivity.KST.SConstruction.loopCollageCrossMap_evaluation
#print axioms SerrePositivity.KST.SConstruction.loopCollageCrossMap_evaluation

#check @SerrePositivity.KST.SConstruction.enrichedCollageUnderlying_map_unit
#print axioms SerrePositivity.KST.SConstruction.enrichedCollageUnderlying_map_unit

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageCross
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageCross

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageBottom_map
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageBottom_map

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageTop_map
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageTop_map

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageCross_pre
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageCross_pre

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageCross_post
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageCross_post

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageComparison
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageComparison

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageComparisonHomotopy
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageComparisonHomotopy

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageComparisonHomotopy_h
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageComparisonHomotopy_h

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageComparisonHomotopy_vertex_edge
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageComparisonHomotopy_vertex_edge

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageInputHomotopy
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageInputHomotopy

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageTransportHomotopy
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageTransportHomotopy

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageTransportTriangle
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageTransportTriangle

#check @SerrePositivity.KST.SConstruction.boundaryCollageTransport_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.boundaryCollageTransport_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyCollageHomotopy
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyCollageHomotopy

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyCollageTriangle
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyCollageTriangle

#check @SerrePositivity.KST.SConstruction.boundaryAssemblySuspensionTransportHomotopy
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblySuspensionTransportHomotopy

#check @SerrePositivity.KST.SConstruction.boundaryAssemblySuspensionTransportHomotopy_h
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblySuspensionTransportHomotopy_h

#check @SerrePositivity.KST.SConstruction.enrichedNerveMap_edge
#print axioms SerrePositivity.KST.SConstruction.enrichedNerveMap_edge

#check @SerrePositivity.KST.SConstruction.strictCoherentDiagram_postcomp_vertex
#print axioms SerrePositivity.KST.SConstruction.strictCoherentDiagram_postcomp_vertex

#check @SerrePositivity.KST.SConstruction.homotopyVertexEdge_postcomp
#print axioms SerrePositivity.KST.SConstruction.homotopyVertexEdge_postcomp

#check @SerrePositivity.KST.SConstruction.homotopyVertexEdge_yoneda
#print axioms SerrePositivity.KST.SConstruction.homotopyVertexEdge_yoneda

#check @SerrePositivity.KST.SConstruction.homotopyCompositionTriangle_vertex
#print axioms SerrePositivity.KST.SConstruction.homotopyCompositionTriangle_vertex

#check @SerrePositivity.KST.SConstruction.homotopyCompositionTriangle_vertex_hom
#print axioms SerrePositivity.KST.SConstruction.homotopyCompositionTriangle_vertex_hom

#check @SerrePositivity.KST.SConstruction.exists_homotopy_specified_vertex_edges
#print axioms SerrePositivity.KST.SConstruction.exists_homotopy_specified_vertex_edges

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageCrossVertexEdge
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageCrossVertexEdge

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageTransport_vertex_hom
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageTransport_vertex_hom

#check @SerrePositivity.KST.SConstruction.exists_enrichedFunctorCollageTransport_specified_components
#print axioms SerrePositivity.KST.SConstruction.exists_enrichedFunctorCollageTransport_specified_components

#check @SerrePositivity.KST.SConstruction.loopCollageCrossEvaluation_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.loopCollageCrossEvaluation_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageCross_loop
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageCross_loop

#check @SerrePositivity.KST.SConstruction.enrichedFunctorCollageCross_loop_evaluation
#print axioms SerrePositivity.KST.SConstruction.enrichedFunctorCollageCross_loop_evaluation

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyCollageCorrection
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyCollageCorrection

#check @SerrePositivity.KST.SConstruction.boundaryAssemblySpecifiedCollageHomotopy
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblySpecifiedCollageHomotopy

#check @SerrePositivity.KST.SConstruction.boundaryAssemblySpecifiedCollageHomotopy_vertex_edge
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblySpecifiedCollageHomotopy_vertex_edge

#check @SerrePositivity.KST.SConstruction.boundaryAssemblySpecifiedCollageHomotopy_hom
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblySpecifiedCollageHomotopy_hom

#check @SerrePositivity.KST.SConstruction.boundaryOriginalSuspension_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.boundaryOriginalSuspension_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionHomotopy
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionHomotopy

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionHomotopy_h
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionHomotopy_h

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionHomotopy_vertex_edge
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionHomotopy_vertex_edge

#check @SerrePositivity.KST.SConstruction.homotopySimplexPrism
#print axioms SerrePositivity.KST.SConstruction.homotopySimplexPrism

#check @SerrePositivity.KST.SConstruction.homotopySimplexPrism_zero
#print axioms SerrePositivity.KST.SConstruction.homotopySimplexPrism_zero

#check @SerrePositivity.KST.SConstruction.homotopySimplexPrism_one
#print axioms SerrePositivity.KST.SConstruction.homotopySimplexPrism_one

#check @SerrePositivity.KST.SConstruction.homotopySimplexPrism_naturality
#print axioms SerrePositivity.KST.SConstruction.homotopySimplexPrism_naturality

#check @SerrePositivity.KST.SConstruction.homotopy_vertex_restriction
#print axioms SerrePositivity.KST.SConstruction.homotopy_vertex_restriction

#check @SerrePositivity.KST.SConstruction.homotopySimplexPrism_vertex
#print axioms SerrePositivity.KST.SConstruction.homotopySimplexPrism_vertex

#check @SerrePositivity.KST.SConstruction.suspensionCoherentDiagram_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.suspensionCoherentDiagram_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.suspensionHom_vertex
#print axioms SerrePositivity.KST.SConstruction.suspensionHom_vertex

#check @SerrePositivity.KST.SConstruction.suspensionEnrichedUnderlying_map
#print axioms SerrePositivity.KST.SConstruction.suspensionEnrichedUnderlying_map

#check @SerrePositivity.KST.SConstruction.suspensionEnrichedUnderlying_eq
#print axioms SerrePositivity.KST.SConstruction.suspensionEnrichedUnderlying_eq

#check @SerrePositivity.KST.SConstruction.pointedKanInclusionUnderlying_map
#print axioms SerrePositivity.KST.SConstruction.pointedKanInclusionUnderlying_map

#check @SerrePositivity.KST.SConstruction.pointedKanInclusion_coherentDiagram
#print axioms SerrePositivity.KST.SConstruction.pointedKanInclusion_coherentDiagram

#check @SerrePositivity.KST.SConstruction.boundarySuspensionPrisms_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.boundarySuspensionPrisms_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionPrism
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionPrism

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionPrism_zero
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionPrism_zero

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionPrism_one
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionPrism_one

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionPrism_naturality
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionPrism_naturality

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionPrism_vertex
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionPrism_vertex

#check @SerrePositivity.KST.SConstruction.boundarySuspensionSquares_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.boundarySuspensionSquares_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare_zero
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare_zero

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare_one
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare_one

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare_left
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare_left

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare_right
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare_right

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare_comp_first
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare_comp_first

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare_comp_second
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare_comp_second

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare_comp_composite
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare_comp_composite

#check @SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare_id
#print axioms SerrePositivity.KST.SConstruction.boundaryAssemblyOriginalSuspensionSquare_id

#check @SerrePositivity.KST.SConstruction.kOriginalSuspension_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kOriginalSuspension_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kKanZeroSuspensionTransformation
#print axioms SerrePositivity.KST.SConstruction.kKanZeroSuspensionTransformation

#check @SerrePositivity.KST.SConstruction.kKanZeroSuspensionTransformation_app
#print axioms SerrePositivity.KST.SConstruction.kKanZeroSuspensionTransformation_app

#check @SerrePositivity.KST.SConstruction.kKanZeroSuspensionHomotopy
#print axioms SerrePositivity.KST.SConstruction.kKanZeroSuspensionHomotopy

#check @SerrePositivity.KST.SConstruction.kKanZeroSuspensionHomotopy_vertex_edge
#print axioms SerrePositivity.KST.SConstruction.kKanZeroSuspensionHomotopy_vertex_edge

#check @SerrePositivity.KST.SConstruction.kKanOriginalSuspensionHomotopy
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalSuspensionHomotopy

#check @SerrePositivity.KST.SConstruction.kKanOriginalSuspensionHomotopy_vertex_edge
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalSuspensionHomotopy_vertex_edge

#check @SerrePositivity.KST.SConstruction.kOriginalSuspensionPrisms_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kOriginalSuspensionPrisms_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalSuspensionPrism
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalSuspensionPrism

#check @SerrePositivity.KST.SConstruction.kKanOriginalSuspensionPrism_zero
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalSuspensionPrism_zero

#check @SerrePositivity.KST.SConstruction.kKanOriginalSuspensionPrism_one
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalSuspensionPrism_one

#check @SerrePositivity.KST.SConstruction.kKanOriginalSuspensionPrism_naturality
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalSuspensionPrism_naturality

#check @SerrePositivity.KST.SConstruction.kKanOriginalSuspensionPrism_vertex
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalSuspensionPrism_vertex

#check @SerrePositivity.KST.SConstruction.kKanOriginalSuspensionPrism_succ
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalSuspensionPrism_succ

#check @SerrePositivity.KST.SConstruction.kKanOriginalSuspensionPrism_zero_stage
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalSuspensionPrism_zero_stage

#check @SerrePositivity.KST.SConstruction.kKanCoherentLevelDiagram_inclusion
#print axioms SerrePositivity.KST.SConstruction.kKanCoherentLevelDiagram_inclusion

#check @SerrePositivity.KST.SConstruction.exists_relative_fibration_family_transport
#print axioms SerrePositivity.KST.SConstruction.exists_relative_fibration_family_transport

#check @SerrePositivity.KST.SConstruction.exists_relative_pointed_family_adjustment
#print axioms SerrePositivity.KST.SConstruction.exists_relative_pointed_family_adjustment

#check @SerrePositivity.KST.SConstruction.RelativeFamilyChain
#print axioms SerrePositivity.KST.SConstruction.RelativeFamilyChain

#check @SerrePositivity.KST.SConstruction.relativeFamilyChainSingle
#print axioms SerrePositivity.KST.SConstruction.relativeFamilyChainSingle

#check @SerrePositivity.KST.SConstruction.relativeFamilyChainAppend
#print axioms SerrePositivity.KST.SConstruction.relativeFamilyChainAppend

#check @SerrePositivity.KST.SConstruction.relativeFamilyChainMap
#print axioms SerrePositivity.KST.SConstruction.relativeFamilyChainMap

#check @SerrePositivity.KST.SConstruction.relativeFamilyChain_boundary
#print axioms SerrePositivity.KST.SConstruction.relativeFamilyChain_boundary

#check @SerrePositivity.KST.SConstruction.exists_relativeFamilyChain_lift
#print axioms SerrePositivity.KST.SConstruction.exists_relativeFamilyChain_lift

#check @SerrePositivity.KST.SConstruction.RelativeSequenceFamilyStage
#print axioms SerrePositivity.KST.SConstruction.RelativeSequenceFamilyStage

#check @SerrePositivity.KST.SConstruction.relativeSequenceFamilyNext
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceFamilyNext

#check @SerrePositivity.KST.SConstruction.relativeSequenceFamilyStage
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceFamilyStage

#check @SerrePositivity.KST.SConstruction.relativeSequenceFamilyRectification
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceFamilyRectification

#check @SerrePositivity.KST.SConstruction.relativeSequenceFamilyRectification_evaluation
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceFamilyRectification_evaluation

#check @SerrePositivity.KST.SConstruction.relativeSequenceFamilyRectification_boundary
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceFamilyRectification_boundary

#check @SerrePositivity.KST.SConstruction.relativeSequenceFamilyRectification_chain
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceFamilyRectification_chain

#check @SerrePositivity.KST.SConstruction.relativeSequenceFamilyRectification_zero
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceFamilyRectification_zero

#check @SerrePositivity.KST.SConstruction.kRawMappingProjection
#print axioms SerrePositivity.KST.SConstruction.kRawMappingProjection

#check @SerrePositivity.KST.SConstruction.kRawMappingProjection_rlp
#print axioms SerrePositivity.KST.SConstruction.kRawMappingProjection_rlp

#check @SerrePositivity.KST.SConstruction.kRawMappingProjection_evaluation
#print axioms SerrePositivity.KST.SConstruction.kRawMappingProjection_evaluation

#check @SerrePositivity.KST.SConstruction.kRelativeFamilyLiftData
#print axioms SerrePositivity.KST.SConstruction.kRelativeFamilyLiftData

#check @SerrePositivity.KST.SConstruction.kRelativeFamilyLiftData_evaluation
#print axioms SerrePositivity.KST.SConstruction.kRelativeFamilyLiftData_evaluation

#check @SerrePositivity.KST.SConstruction.relativeKFamilyRectificationData
#print axioms SerrePositivity.KST.SConstruction.relativeKFamilyRectificationData

#check @SerrePositivity.KST.SConstruction.relativeKFamilyRectificationData_boundary
#print axioms SerrePositivity.KST.SConstruction.relativeKFamilyRectificationData_boundary

#check @SerrePositivity.KST.SConstruction.relativeKFamilyRectificationData_projection
#print axioms SerrePositivity.KST.SConstruction.relativeKFamilyRectificationData_projection

#check @SerrePositivity.KST.SConstruction.relativeKFamilyRectificationData_chain
#print axioms SerrePositivity.KST.SConstruction.relativeKFamilyRectificationData_chain

#check @SerrePositivity.KST.SConstruction.RelativeFamilyChain.nil
#print axioms SerrePositivity.KST.SConstruction.RelativeFamilyChain.nil

#check @SerrePositivity.KST.SConstruction.RelativeFamilyChain.cons
#print axioms SerrePositivity.KST.SConstruction.RelativeFamilyChain.cons

#check @SerrePositivity.KST.SConstruction.relativeFamilyChainTrace
#print axioms SerrePositivity.KST.SConstruction.relativeFamilyChainTrace

#check @SerrePositivity.KST.SConstruction.exists_relativeFamilyChain_lift_with_trace
#print axioms SerrePositivity.KST.SConstruction.exists_relativeFamilyChain_lift_with_trace

#check @SerrePositivity.KST.SConstruction.RelativeSequenceFamilyStage.val
#print axioms SerrePositivity.KST.SConstruction.RelativeSequenceFamilyStage.val

#check @SerrePositivity.KST.SConstruction.RelativeSequenceFamilyStage.chain
#print axioms SerrePositivity.KST.SConstruction.RelativeSequenceFamilyStage.chain

#check @SerrePositivity.KST.SConstruction.relativeSequenceFamilyNext_trace
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceFamilyNext_trace

#check @SerrePositivity.KST.SConstruction.coherentEndpointPath
#print axioms SerrePositivity.KST.SConstruction.coherentEndpointPath

#check @SerrePositivity.KST.SConstruction.coherentEndpointPath_map
#print axioms SerrePositivity.KST.SConstruction.coherentEndpointPath_map

#check @SerrePositivity.KST.SConstruction.coherentSimplexArrow
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexArrow

#check @SerrePositivity.KST.SConstruction.coherentSimplexArrow_edge
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexArrow_edge

#check @SerrePositivity.KST.SConstruction.coherentSimplexArrow_naturality
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexArrow_naturality

#check @SerrePositivity.KST.SConstruction.coherentEndpointPathComposite
#print axioms SerrePositivity.KST.SConstruction.coherentEndpointPathComposite

#check @SerrePositivity.KST.SConstruction.coherentEndpointPathToComposite
#print axioms SerrePositivity.KST.SConstruction.coherentEndpointPathToComposite

#check @SerrePositivity.KST.SConstruction.coherentSimplexCompositionEdge
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexCompositionEdge

#check @SerrePositivity.KST.SConstruction.coherentSimplexArrow_heq
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexArrow_heq

#check @SerrePositivity.KST.SConstruction.coherentSimplexArrow_of_edge_face
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexArrow_of_edge_face

#check @SerrePositivity.KST.SConstruction.coherentTriangleMappingEdge
#print axioms SerrePositivity.KST.SConstruction.coherentTriangleMappingEdge

#check @SerrePositivity.KST.SConstruction.CoherentSquareMappingTriangles
#print axioms SerrePositivity.KST.SConstruction.CoherentSquareMappingTriangles

#check @SerrePositivity.KST.SConstruction.coherentSquareMappingBottomRight
#print axioms SerrePositivity.KST.SConstruction.coherentSquareMappingBottomRight

#check @SerrePositivity.KST.SConstruction.coherentSquareMappingLeftTop
#print axioms SerrePositivity.KST.SConstruction.coherentSquareMappingLeftTop

#check @SerrePositivity.KST.SConstruction.coherentSquareMappingTrianglesOfEdges
#print axioms SerrePositivity.KST.SConstruction.coherentSquareMappingTrianglesOfEdges

#check @SerrePositivity.KST.SConstruction.squareHorizontalEdge_yoneda
#print axioms SerrePositivity.KST.SConstruction.squareHorizontalEdge_yoneda

#check @SerrePositivity.KST.SConstruction.squareVerticalEdge_yoneda
#print axioms SerrePositivity.KST.SConstruction.squareVerticalEdge_yoneda

#check @SerrePositivity.KST.SConstruction.coherentSquareMappingTrianglesOfBoundary
#print axioms SerrePositivity.KST.SConstruction.coherentSquareMappingTrianglesOfBoundary

#check @SerrePositivity.KST.SConstruction.kSuspensionMappingTriangles_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kSuspensionMappingTriangles_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalSuspensionSquare
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalSuspensionSquare

#check @SerrePositivity.KST.SConstruction.kKanOriginalSuspensionSquare_zero
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalSuspensionSquare_zero

#check @SerrePositivity.KST.SConstruction.kKanOriginalSuspensionSquare_one
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalSuspensionSquare_one

#check @SerrePositivity.KST.SConstruction.kKanOriginalSuspensionSquare_left
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalSuspensionSquare_left

#check @SerrePositivity.KST.SConstruction.kKanOriginalSuspensionSquare_right
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalSuspensionSquare_right

#check @SerrePositivity.KST.SConstruction.kKanSuspensionMappingTriangles
#print axioms SerrePositivity.KST.SConstruction.kKanSuspensionMappingTriangles

#check @SerrePositivity.KST.SConstruction.KanMappingSpanComposition
#print axioms SerrePositivity.KST.SConstruction.KanMappingSpanComposition

#check @SerrePositivity.KST.SConstruction.kanMappingSpanComposition
#print axioms SerrePositivity.KST.SConstruction.kanMappingSpanComposition

#check @SerrePositivity.KST.SConstruction.kSuspensionCompatibility_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kSuspensionCompatibility_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kKanSuspensionCompatibilityComposition
#print axioms SerrePositivity.KST.SConstruction.kKanSuspensionCompatibilityComposition

#check @SerrePositivity.KST.SConstruction.kKanSuspensionCompatibilityEdge
#print axioms SerrePositivity.KST.SConstruction.kKanSuspensionCompatibilityEdge

#check @SerrePositivity.KST.SConstruction.kKanSuspensionCompatibilityHomotopy
#print axioms SerrePositivity.KST.SConstruction.kKanSuspensionCompatibilityHomotopy

#check @SerrePositivity.KST.SConstruction.kKanSuspensionCompatibilityHomotopy_base
#print axioms SerrePositivity.KST.SConstruction.kKanSuspensionCompatibilityHomotopy_base

#check @SerrePositivity.KST.SConstruction.sequenceCompatibilityEdge_precompose
#print axioms SerrePositivity.KST.SConstruction.sequenceCompatibilityEdge_precompose

#check @SerrePositivity.KST.SConstruction.monicKPrismCompatibilityEdge
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompatibilityEdge

#check @SerrePositivity.KST.SConstruction.monicKPrismCompatibilityHomotopy
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompatibilityHomotopy

#check @SerrePositivity.KST.SConstruction.monicKPrismCompatibilityHomotopy_base
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompatibilityHomotopy_base

#check @SerrePositivity.KST.SConstruction.CoherentSquareMappingTriangles.mk
#print axioms SerrePositivity.KST.SConstruction.CoherentSquareMappingTriangles.mk

#check @SerrePositivity.KST.SConstruction.CoherentSquareMappingTriangles.diagonal
#print axioms SerrePositivity.KST.SConstruction.CoherentSquareMappingTriangles.diagonal

#check @SerrePositivity.KST.SConstruction.CoherentSquareMappingTriangles.bottomRight
#print axioms SerrePositivity.KST.SConstruction.CoherentSquareMappingTriangles.bottomRight

#check @SerrePositivity.KST.SConstruction.CoherentSquareMappingTriangles.leftTop
#print axioms SerrePositivity.KST.SConstruction.CoherentSquareMappingTriangles.leftTop

#check @SerrePositivity.KST.SConstruction.KanMappingSpanComposition.mk
#print axioms SerrePositivity.KST.SConstruction.KanMappingSpanComposition.mk

#check @SerrePositivity.KST.SConstruction.KanMappingSpanComposition.inverse
#print axioms SerrePositivity.KST.SConstruction.KanMappingSpanComposition.inverse

#check @SerrePositivity.KST.SConstruction.KanMappingSpanComposition.inverseLeft
#print axioms SerrePositivity.KST.SConstruction.KanMappingSpanComposition.inverseLeft

#check @SerrePositivity.KST.SConstruction.KanMappingSpanComposition.inverseRight
#print axioms SerrePositivity.KST.SConstruction.KanMappingSpanComposition.inverseRight

#check @SerrePositivity.KST.SConstruction.KanMappingSpanComposition.edge
#print axioms SerrePositivity.KST.SConstruction.KanMappingSpanComposition.edge

#check @SerrePositivity.KST.SConstruction.KanMappingSpanComposition.triangle
#print axioms SerrePositivity.KST.SConstruction.KanMappingSpanComposition.triangle

#check @SerrePositivity.KST.SConstruction.exists_kanFibration_liftOuterTriangle
#print axioms SerrePositivity.KST.SConstruction.exists_kanFibration_liftOuterTriangle

#check @SerrePositivity.KST.SConstruction.exists_kanFibration_liftCompositionTriangle
#print axioms SerrePositivity.KST.SConstruction.exists_kanFibration_liftCompositionTriangle

#check @SerrePositivity.KST.SConstruction.KanSpanTriangleData
#print axioms SerrePositivity.KST.SConstruction.KanSpanTriangleData

#check @SerrePositivity.KST.SConstruction.kanSpanTriangleDataOfComposition
#print axioms SerrePositivity.KST.SConstruction.kanSpanTriangleDataOfComposition

#check @SerrePositivity.KST.SConstruction.exists_kanSpanTriangleData_lift
#print axioms SerrePositivity.KST.SConstruction.exists_kanSpanTriangleData_lift

#check @SerrePositivity.KST.SConstruction.KanSpanTriangleDataOver
#print axioms SerrePositivity.KST.SConstruction.KanSpanTriangleDataOver

#check @SerrePositivity.KST.SConstruction.kanSpanTriangleDataLift
#print axioms SerrePositivity.KST.SConstruction.kanSpanTriangleDataLift

#check @SerrePositivity.KST.SConstruction.relativeKanSpanFamilyData
#print axioms SerrePositivity.KST.SConstruction.relativeKanSpanFamilyData

#check @SerrePositivity.KST.SConstruction.relativeKanHomotopySpanData
#print axioms SerrePositivity.KST.SConstruction.relativeKanHomotopySpanData

#check @SerrePositivity.KST.SConstruction.relativeKanHomotopySpanComposite
#print axioms SerrePositivity.KST.SConstruction.relativeKanHomotopySpanComposite

#check @SerrePositivity.KST.SConstruction.relativeKanHomotopySpanBoundary
#print axioms SerrePositivity.KST.SConstruction.relativeKanHomotopySpanBoundary

#check @SerrePositivity.KST.SConstruction.relativeKanHomotopySpanComposite_restrict
#print axioms SerrePositivity.KST.SConstruction.relativeKanHomotopySpanComposite_restrict

#check @SerrePositivity.KST.SConstruction.relativeKanHomotopySpanComposite_restrict_constant
#print axioms SerrePositivity.KST.SConstruction.relativeKanHomotopySpanComposite_restrict_constant

#check @SerrePositivity.KST.SConstruction.relativeSequenceSpanHomotopy
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceSpanHomotopy

#check @SerrePositivity.KST.SConstruction.relativeSequenceSpanHomotopy_boundary
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceSpanHomotopy_boundary

#check @SerrePositivity.KST.SConstruction.relativeSequenceSpanRectification
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceSpanRectification

#check @SerrePositivity.KST.SConstruction.relativeSequenceSpanRectification_boundary
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceSpanRectification_boundary

#check @SerrePositivity.KST.SConstruction.relativeSequenceSpanRectification_chain
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceSpanRectification_chain

#check @SerrePositivity.KST.SConstruction.relativeSequenceSpanRectification_zero
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceSpanRectification_zero

#check @SerrePositivity.KST.SConstruction.relativeKSpanFamilyRectificationData
#print axioms SerrePositivity.KST.SConstruction.relativeKSpanFamilyRectificationData

#check @SerrePositivity.KST.SConstruction.relativeKSpanFamilyRectificationData_boundary
#print axioms SerrePositivity.KST.SConstruction.relativeKSpanFamilyRectificationData_boundary

#check @SerrePositivity.KST.SConstruction.relativeKSpanFamilyRectificationData_projection
#print axioms SerrePositivity.KST.SConstruction.relativeKSpanFamilyRectificationData_projection

#check @SerrePositivity.KST.SConstruction.KanSpanTriangleData.mk
#print axioms SerrePositivity.KST.SConstruction.KanSpanTriangleData.mk

#check @SerrePositivity.KST.SConstruction.KanSpanTriangleData.inverse
#print axioms SerrePositivity.KST.SConstruction.KanSpanTriangleData.inverse

#check @SerrePositivity.KST.SConstruction.KanSpanTriangleData.inverseTriangle
#print axioms SerrePositivity.KST.SConstruction.KanSpanTriangleData.inverseTriangle

#check @SerrePositivity.KST.SConstruction.KanSpanTriangleData.edge
#print axioms SerrePositivity.KST.SConstruction.KanSpanTriangleData.edge

#check @SerrePositivity.KST.SConstruction.KanSpanTriangleData.compositionTriangle
#print axioms SerrePositivity.KST.SConstruction.KanSpanTriangleData.compositionTriangle

#check @SerrePositivity.KST.SConstruction.KanSpanTriangleDataOver.mk
#print axioms SerrePositivity.KST.SConstruction.KanSpanTriangleDataOver.mk

#check @SerrePositivity.KST.SConstruction.KanSpanTriangleDataOver.data
#print axioms SerrePositivity.KST.SConstruction.KanSpanTriangleDataOver.data

#check @SerrePositivity.KST.SConstruction.KanSpanTriangleDataOver.inverse_edge
#print axioms SerrePositivity.KST.SConstruction.KanSpanTriangleDataOver.inverse_edge

#check @SerrePositivity.KST.SConstruction.KanSpanTriangleDataOver.inverse_triangle
#print axioms SerrePositivity.KST.SConstruction.KanSpanTriangleDataOver.inverse_triangle

#check @SerrePositivity.KST.SConstruction.KanSpanTriangleDataOver.composite_edge
#print axioms SerrePositivity.KST.SConstruction.KanSpanTriangleDataOver.composite_edge

#check @SerrePositivity.KST.SConstruction.KanSpanTriangleDataOver.composition_triangle
#print axioms SerrePositivity.KST.SConstruction.KanSpanTriangleDataOver.composition_triangle

#check @SerrePositivity.KST.SConstruction.equivalenceFamilyPathHomotopy
#print axioms SerrePositivity.KST.SConstruction.equivalenceFamilyPathHomotopy

#check @SerrePositivity.KST.SConstruction.equivalenceFamilyPathHomotopy_section
#print axioms SerrePositivity.KST.SConstruction.equivalenceFamilyPathHomotopy_section

#check @SerrePositivity.KST.SConstruction.equivalenceFamilyPathHomotopy_precomp
#print axioms SerrePositivity.KST.SConstruction.equivalenceFamilyPathHomotopy_precomp

#check @SerrePositivity.KST.SConstruction.equivalenceFamilyPathHomotopy_section_pre
#print axioms SerrePositivity.KST.SConstruction.equivalenceFamilyPathHomotopy_section_pre

#check @SerrePositivity.KST.SConstruction.relativeEquivalenceFamilyPathLift
#print axioms SerrePositivity.KST.SConstruction.relativeEquivalenceFamilyPathLift

#check @SerrePositivity.KST.SConstruction.RelativeEquivalenceFamilyData
#print axioms SerrePositivity.KST.SConstruction.RelativeEquivalenceFamilyData

#check @SerrePositivity.KST.SConstruction.relativeEquivalenceFamilyRecovery
#print axioms SerrePositivity.KST.SConstruction.relativeEquivalenceFamilyRecovery

#check @SerrePositivity.KST.SConstruction.coherentMappingIntervalComparison
#print axioms SerrePositivity.KST.SConstruction.coherentMappingIntervalComparison

#check @SerrePositivity.KST.SConstruction.coherentMappingIntervalComparison_isQCatEquivalence
#print axioms SerrePositivity.KST.SConstruction.coherentMappingIntervalComparison_isQCatEquivalence

#check @SerrePositivity.KST.SConstruction.relativeCoherentIntervalFamilyRecovery
#print axioms SerrePositivity.KST.SConstruction.relativeCoherentIntervalFamilyRecovery

#check @SerrePositivity.KST.SConstruction.relativeCoherentCylinderFamilyRecovery
#print axioms SerrePositivity.KST.SConstruction.relativeCoherentCylinderFamilyRecovery

#check @SerrePositivity.KST.SConstruction.loopCollageSuspensionIntervalComparison
#print axioms SerrePositivity.KST.SConstruction.loopCollageSuspensionIntervalComparison

#check @SerrePositivity.KST.SConstruction.loopCollageSuspensionIntervalComparison_isQCatEquivalence
#print axioms SerrePositivity.KST.SConstruction.loopCollageSuspensionIntervalComparison_isQCatEquivalence

#check @SerrePositivity.KST.SConstruction.relativeLoopCollageSuspensionFamilyRecovery
#print axioms SerrePositivity.KST.SConstruction.relativeLoopCollageSuspensionFamilyRecovery

#check @SerrePositivity.KST.SConstruction.RelativeEquivalenceFamilyData.mk
#print axioms SerrePositivity.KST.SConstruction.RelativeEquivalenceFamilyData.mk

#check @SerrePositivity.KST.SConstruction.RelativeEquivalenceFamilyData.family
#print axioms SerrePositivity.KST.SConstruction.RelativeEquivalenceFamilyData.family

#check @SerrePositivity.KST.SConstruction.RelativeEquivalenceFamilyData.boundary
#print axioms SerrePositivity.KST.SConstruction.RelativeEquivalenceFamilyData.boundary

#check @SerrePositivity.KST.SConstruction.RelativeEquivalenceFamilyData.comparison
#print axioms SerrePositivity.KST.SConstruction.RelativeEquivalenceFamilyData.comparison

#check @SerrePositivity.KST.SConstruction.RelativeEquivalenceFamilyData.comparison_boundary
#print axioms SerrePositivity.KST.SConstruction.RelativeEquivalenceFamilyData.comparison_boundary

#check @SerrePositivity.KST.SConstruction.coherentPathInsert
#print axioms SerrePositivity.KST.SConstruction.coherentPathInsert

#check @SerrePositivity.KST.SConstruction.coherentPathInsertFunctor
#print axioms SerrePositivity.KST.SConstruction.coherentPathInsertFunctor

#check @SerrePositivity.KST.SConstruction.coherentPathInsertTransformation
#print axioms SerrePositivity.KST.SConstruction.coherentPathInsertTransformation

#check @SerrePositivity.KST.SConstruction.coherentPathInsert_eq
#print axioms SerrePositivity.KST.SConstruction.coherentPathInsert_eq

#check @SerrePositivity.KST.SConstruction.coherentPathInsertionHomotopy
#print axioms SerrePositivity.KST.SConstruction.coherentPathInsertionHomotopy

#check @SerrePositivity.KST.SConstruction.coherentPathInsertThrough
#print axioms SerrePositivity.KST.SConstruction.coherentPathInsertThrough

#check @SerrePositivity.KST.SConstruction.coherentPathInsertThrough_ι
#print axioms SerrePositivity.KST.SConstruction.coherentPathInsertThrough_ι

#check @SerrePositivity.KST.SConstruction.coherentPathInsertionHomotopy_relative
#print axioms SerrePositivity.KST.SConstruction.coherentPathInsertionHomotopy_relative

#check @SerrePositivity.KST.SConstruction.coherentPathInsert_map
#print axioms SerrePositivity.KST.SConstruction.coherentPathInsert_map

#check @SerrePositivity.KST.SConstruction.coherentPathInsertionHomotopy_naturality
#print axioms SerrePositivity.KST.SConstruction.coherentPathInsertionHomotopy_naturality

#check @SerrePositivity.KST.SConstruction.coherentPathInsert_endpoint
#print axioms SerrePositivity.KST.SConstruction.coherentPathInsert_endpoint

#check @SerrePositivity.KST.SConstruction.coherentPathInsertionHomotopy_endpoint_edge
#print axioms SerrePositivity.KST.SConstruction.coherentPathInsertionHomotopy_endpoint_edge

#check @SerrePositivity.KST.SConstruction.coherentPathCutSplit
#print axioms SerrePositivity.KST.SConstruction.coherentPathCutSplit

#check @SerrePositivity.KST.SConstruction.coherentPathCutSplit_comp
#print axioms SerrePositivity.KST.SConstruction.coherentPathCutSplit_comp

#check @SerrePositivity.KST.SConstruction.coherentPathCutSplit_mapping
#print axioms SerrePositivity.KST.SConstruction.coherentPathCutSplit_mapping

#check @SerrePositivity.KST.SConstruction.coherentPathMappingCutHomotopy
#print axioms SerrePositivity.KST.SConstruction.coherentPathMappingCutHomotopy

#check @SerrePositivity.KST.SConstruction.coherentPathMappingCutHomotopy_relative
#print axioms SerrePositivity.KST.SConstruction.coherentPathMappingCutHomotopy_relative

#check @SerrePositivity.KST.SConstruction.coherentPathMappingCutHomotopy_reindex
#print axioms SerrePositivity.KST.SConstruction.coherentPathMappingCutHomotopy_reindex

#check @SerrePositivity.KST.SConstruction.coherentPathMappingCutHomotopy_vertex
#print axioms SerrePositivity.KST.SConstruction.coherentPathMappingCutHomotopy_vertex

#check @SerrePositivity.KST.SConstruction.coherentPathMappingCutHomotopy_endpoint_edge
#print axioms SerrePositivity.KST.SConstruction.coherentPathMappingCutHomotopy_endpoint_edge

#check @SerrePositivity.KST.SConstruction.coherentPathMappingCutHomotopy_heq
#print axioms SerrePositivity.KST.SConstruction.coherentPathMappingCutHomotopy_heq

#check @SerrePositivity.KST.SConstruction.coherentDiagramPathFamily
#print axioms SerrePositivity.KST.SConstruction.coherentDiagramPathFamily

#check @SerrePositivity.KST.SConstruction.coherentDiagramCutHomotopy
#print axioms SerrePositivity.KST.SConstruction.coherentDiagramCutHomotopy

#check @SerrePositivity.KST.SConstruction.coherentDiagramCutHomotopy_relative
#print axioms SerrePositivity.KST.SConstruction.coherentDiagramCutHomotopy_relative

#check @SerrePositivity.KST.SConstruction.coherentDiagramCutHomotopy_endpoint_edge
#print axioms SerrePositivity.KST.SConstruction.coherentDiagramCutHomotopy_endpoint_edge

#check @SerrePositivity.KST.SConstruction.coherentDiagramCutHomotopy_naturality
#print axioms SerrePositivity.KST.SConstruction.coherentDiagramCutHomotopy_naturality

#check @SerrePositivity.KST.SConstruction.kPrismPathDecoding_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kPrismPathDecoding_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kKanPrismCutHomotopy
#print axioms SerrePositivity.KST.SConstruction.kKanPrismCutHomotopy

#check @SerrePositivity.KST.SConstruction.kKanPrismCutHomotopy_input_naturality
#print axioms SerrePositivity.KST.SConstruction.kKanPrismCutHomotopy_input_naturality

#check @SerrePositivity.KST.SConstruction.kKanPrismCutHomotopy_naturality
#print axioms SerrePositivity.KST.SConstruction.kKanPrismCutHomotopy_naturality

#check @SerrePositivity.KST.SConstruction.kKanPrismCutHomotopy_endpoint_edge
#print axioms SerrePositivity.KST.SConstruction.kKanPrismCutHomotopy_endpoint_edge

#check @SerrePositivity.KST.SConstruction.fixedHomotopySpanEdge
#print axioms SerrePositivity.KST.SConstruction.fixedHomotopySpanEdge

#check @SerrePositivity.KST.SConstruction.fixedKanSpanTriangleData
#print axioms SerrePositivity.KST.SConstruction.fixedKanSpanTriangleData

#check @SerrePositivity.KST.SConstruction.fixedKanHomotopySpanBoundary
#print axioms SerrePositivity.KST.SConstruction.fixedKanHomotopySpanBoundary

#check @SerrePositivity.KST.SConstruction.fixedHomotopySpanBoundary_precomp
#print axioms SerrePositivity.KST.SConstruction.fixedHomotopySpanBoundary_precomp

#check @SerrePositivity.KST.SConstruction.fixedHomotopySpanBoundary_target
#print axioms SerrePositivity.KST.SConstruction.fixedHomotopySpanBoundary_target

#check @SerrePositivity.KST.SConstruction.fixedKanHomotopySpanComposite
#print axioms SerrePositivity.KST.SConstruction.fixedKanHomotopySpanComposite

#check @SerrePositivity.KST.SConstruction.fixedKanHomotopySpanComposite_relative
#print axioms SerrePositivity.KST.SConstruction.fixedKanHomotopySpanComposite_relative

#check @SerrePositivity.KST.SConstruction.fixedKanHomotopySpanComposite_relative_source
#print axioms SerrePositivity.KST.SConstruction.fixedKanHomotopySpanComposite_relative_source

#check @SerrePositivity.KST.SConstruction.coherentDoubleCutBoundary
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleCutBoundary

#check @SerrePositivity.KST.SConstruction.coherentDoubleCutHomotopy_left_relative
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleCutHomotopy_left_relative

#check @SerrePositivity.KST.SConstruction.coherentDoubleCutHomotopy_right_relative
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleCutHomotopy_right_relative

#check @SerrePositivity.KST.SConstruction.coherentCutSpanComposite
#print axioms SerrePositivity.KST.SConstruction.coherentCutSpanComposite

#check @SerrePositivity.KST.SConstruction.coherentCutSpanComposite_relative
#print axioms SerrePositivity.KST.SConstruction.coherentCutSpanComposite_relative

#check @SerrePositivity.KST.SConstruction.coherentCutSpanComposite_relative_original
#print axioms SerrePositivity.KST.SConstruction.coherentCutSpanComposite_relative_original

#check @SerrePositivity.KST.SConstruction.kPrismCutSpanFamilies_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kPrismCutSpanFamilies_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrism_top_object
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrism_top_object

#check @SerrePositivity.KST.SConstruction.kKanPrism_top_simplex_object
#print axioms SerrePositivity.KST.SConstruction.kKanPrism_top_simplex_object

#check @SerrePositivity.KST.SConstruction.kKanPrism_top_hom_kanComplex
#print axioms SerrePositivity.KST.SConstruction.kKanPrism_top_hom_kanComplex

#check @SerrePositivity.KST.SConstruction.kKanPrismCutSpanComposite
#print axioms SerrePositivity.KST.SConstruction.kKanPrismCutSpanComposite

#check @SerrePositivity.KST.SConstruction.kKanPrismCutSpanComposite_relative
#print axioms SerrePositivity.KST.SConstruction.kKanPrismCutSpanComposite_relative

#check @SerrePositivity.KST.SConstruction.relativeKFixedSpanFamilyRectificationData
#print axioms SerrePositivity.KST.SConstruction.relativeKFixedSpanFamilyRectificationData

#check @SerrePositivity.KST.SConstruction.relativeKFixedSpanFamilyRectificationData_boundary
#print axioms SerrePositivity.KST.SConstruction.relativeKFixedSpanFamilyRectificationData_boundary

#check @SerrePositivity.KST.SConstruction.relativeKFixedSpanFamilyRectificationData_projection
#print axioms SerrePositivity.KST.SConstruction.relativeKFixedSpanFamilyRectificationData_projection

#check @SerrePositivity.KST.SConstruction.relativeSequenceFixedSpanHomotopy
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceFixedSpanHomotopy

#check @SerrePositivity.KST.SConstruction.relativeSequenceFixedSpanHomotopy_boundary
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceFixedSpanHomotopy_boundary

#check @SerrePositivity.KST.SConstruction.relativeSequenceFixedSpanRectification
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceFixedSpanRectification

#check @SerrePositivity.KST.SConstruction.kanSpanHorn
#print axioms SerrePositivity.KST.SConstruction.kanSpanHorn

#check @SerrePositivity.KST.SConstruction.kanSpanHorn_source
#print axioms SerrePositivity.KST.SConstruction.kanSpanHorn_source

#check @SerrePositivity.KST.SConstruction.kanSpanHorn_target
#print axioms SerrePositivity.KST.SConstruction.kanSpanHorn_target

#check @SerrePositivity.KST.SConstruction.kanSpanPastingChoices
#print axioms SerrePositivity.KST.SConstruction.kanSpanPastingChoices

#check @SerrePositivity.KST.SConstruction.kanSpanPastingChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.kanSpanPastingChoices_isContractibleKan

#check @SerrePositivity.KST.SConstruction.kanSpanPastingChoices_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.kanSpanPastingChoices_relative_lifting

#check @SerrePositivity.KST.SConstruction.kanSpanPastingAt
#print axioms SerrePositivity.KST.SConstruction.kanSpanPastingAt

#check @SerrePositivity.KST.SConstruction.kanSpanPastingAt_source
#print axioms SerrePositivity.KST.SConstruction.kanSpanPastingAt_source

#check @SerrePositivity.KST.SConstruction.kanSpanPastingAt_target
#print axioms SerrePositivity.KST.SConstruction.kanSpanPastingAt_target

#check @SerrePositivity.KST.SConstruction.kanSpanPastedEdge
#print axioms SerrePositivity.KST.SConstruction.kanSpanPastedEdge

#check @SerrePositivity.KST.SConstruction.kanSpanPastedTriangle
#print axioms SerrePositivity.KST.SConstruction.kanSpanPastedTriangle

#check @SerrePositivity.KST.SConstruction.anodyneExtensionVertex
#print axioms SerrePositivity.KST.SConstruction.anodyneExtensionVertex

#check @SerrePositivity.KST.SConstruction.anodyneExtensionAt_vertex
#print axioms SerrePositivity.KST.SConstruction.anodyneExtensionAt_vertex

#check @SerrePositivity.KST.SConstruction.anodyneExtensionFamily
#print axioms SerrePositivity.KST.SConstruction.anodyneExtensionFamily

#check @SerrePositivity.KST.SConstruction.anodyneExtensionFamily_fac
#print axioms SerrePositivity.KST.SConstruction.anodyneExtensionFamily_fac

#check @SerrePositivity.KST.SConstruction.kanSpanTriangle_restrict
#print axioms SerrePositivity.KST.SConstruction.kanSpanTriangle_restrict

#check @SerrePositivity.KST.SConstruction.kanSpanPastingVertex
#print axioms SerrePositivity.KST.SConstruction.kanSpanPastingVertex

#check @SerrePositivity.KST.SConstruction.kanSpanPastingAt_vertex
#print axioms SerrePositivity.KST.SConstruction.kanSpanPastingAt_vertex

#check @SerrePositivity.KST.SConstruction.kanSpanPastedEdge_vertex
#print axioms SerrePositivity.KST.SConstruction.kanSpanPastedEdge_vertex

#check @SerrePositivity.KST.SConstruction.kanSpanPastedTriangle_vertex_simplex
#print axioms SerrePositivity.KST.SConstruction.kanSpanPastedTriangle_vertex_simplex

#check @SerrePositivity.KST.SConstruction.kanMappingSpanOuterTriangle
#print axioms SerrePositivity.KST.SConstruction.kanMappingSpanOuterTriangle

#check @SerrePositivity.KST.SConstruction.kanMappingSpanPastingVertex
#print axioms SerrePositivity.KST.SConstruction.kanMappingSpanPastingVertex

#check @SerrePositivity.KST.SConstruction.kanSpanPastedEdge_mappingSpanVertex
#print axioms SerrePositivity.KST.SConstruction.kanSpanPastedEdge_mappingSpanVertex

#check @SerrePositivity.KST.SConstruction.kanSpanPastingFamily
#print axioms SerrePositivity.KST.SConstruction.kanSpanPastingFamily

#check @SerrePositivity.KST.SConstruction.kanSpanPastingFamily_source
#print axioms SerrePositivity.KST.SConstruction.kanSpanPastingFamily_source

#check @SerrePositivity.KST.SConstruction.kanSpanPastingFamily_target
#print axioms SerrePositivity.KST.SConstruction.kanSpanPastingFamily_target

#check @SerrePositivity.KST.SConstruction.kanSpanPastedEdgeFamily
#print axioms SerrePositivity.KST.SConstruction.kanSpanPastedEdgeFamily

#check @SerrePositivity.KST.SConstruction.kSuspensionSpecifiedPasting_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kSuspensionSpecifiedPasting_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kKanSuspensionPastingChoices
#print axioms SerrePositivity.KST.SConstruction.kKanSuspensionPastingChoices

#check @SerrePositivity.KST.SConstruction.kKanSuspensionPastingChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.kKanSuspensionPastingChoices_isContractibleKan

#check @SerrePositivity.KST.SConstruction.kKanSuspensionSpecifiedPastingVertex
#print axioms SerrePositivity.KST.SConstruction.kKanSuspensionSpecifiedPastingVertex

#check @SerrePositivity.KST.SConstruction.kKanSuspensionSpecifiedPastingVertex_edge
#print axioms SerrePositivity.KST.SConstruction.kKanSuspensionSpecifiedPastingVertex_edge

#check @SerrePositivity.KST.SConstruction.kKanSuspensionPastingChoices_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.kKanSuspensionPastingChoices_relative_lifting

#check @SerrePositivity.KST.SConstruction.kKanSuspensionPastingFamily
#print axioms SerrePositivity.KST.SConstruction.kKanSuspensionPastingFamily

#check @SerrePositivity.KST.SConstruction.kKanSuspensionPastingEdge
#print axioms SerrePositivity.KST.SConstruction.kKanSuspensionPastingEdge

#check @SerrePositivity.KST.SConstruction.kKanSuspensionPastingEdge_specified
#print axioms SerrePositivity.KST.SConstruction.kKanSuspensionPastingEdge_specified

#check @SerrePositivity.KST.SConstruction.kKanSuspensionPastingHomotopy
#print axioms SerrePositivity.KST.SConstruction.kKanSuspensionPastingHomotopy

#check @SerrePositivity.KST.SConstruction.kKanSuspensionPastingHomotopy_specified
#print axioms SerrePositivity.KST.SConstruction.kKanSuspensionPastingHomotopy_specified

#check @SerrePositivity.KST.SConstruction.kKanSuspensionPastingFamily_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.kKanSuspensionPastingFamily_relative_lifting

#check @SerrePositivity.KST.SConstruction.monicKSpanPastingEdge
#print axioms SerrePositivity.KST.SConstruction.monicKSpanPastingEdge

#check @SerrePositivity.KST.SConstruction.monicKSpanPastingEdge_specified
#print axioms SerrePositivity.KST.SConstruction.monicKSpanPastingEdge_specified

#check @SerrePositivity.KST.SConstruction.monicKSpanPastingHomotopy
#print axioms SerrePositivity.KST.SConstruction.monicKSpanPastingHomotopy

#check @SerrePositivity.KST.SConstruction.monicKSpanPastingHomotopy_specified
#print axioms SerrePositivity.KST.SConstruction.monicKSpanPastingHomotopy_specified

#check @SerrePositivity.KST.SConstruction.relativeAnodyneFamilyExtension
#print axioms SerrePositivity.KST.SConstruction.relativeAnodyneFamilyExtension

#check @SerrePositivity.KST.SConstruction.varyingKanSpanHornFamily
#print axioms SerrePositivity.KST.SConstruction.varyingKanSpanHornFamily

#check @SerrePositivity.KST.SConstruction.varyingKanSpanHornFamily_source
#print axioms SerrePositivity.KST.SConstruction.varyingKanSpanHornFamily_source

#check @SerrePositivity.KST.SConstruction.varyingKanSpanHornFamily_target
#print axioms SerrePositivity.KST.SConstruction.varyingKanSpanHornFamily_target

#check @SerrePositivity.KST.SConstruction.relativeVaryingKanSpanTriangleFamily
#print axioms SerrePositivity.KST.SConstruction.relativeVaryingKanSpanTriangleFamily

#check @SerrePositivity.KST.SConstruction.relativeVaryingKanSpanTriangleFamily_source
#print axioms SerrePositivity.KST.SConstruction.relativeVaryingKanSpanTriangleFamily_source

#check @SerrePositivity.KST.SConstruction.relativeVaryingKanSpanTriangleFamily_target
#print axioms SerrePositivity.KST.SConstruction.relativeVaryingKanSpanTriangleFamily_target

#check @SerrePositivity.KST.SConstruction.kanSpanHorn_postcomp
#print axioms SerrePositivity.KST.SConstruction.kanSpanHorn_postcomp

#check @SerrePositivity.KST.SConstruction.varyingKanSpanEdge_precomp
#print axioms SerrePositivity.KST.SConstruction.varyingKanSpanEdge_precomp

#check @SerrePositivity.KST.SConstruction.varyingKanSpanHornFamily_naturality
#print axioms SerrePositivity.KST.SConstruction.varyingKanSpanHornFamily_naturality

#check @SerrePositivity.KST.SConstruction.relativeKanOuterSpanFamilyData
#print axioms SerrePositivity.KST.SConstruction.relativeKanOuterSpanFamilyData

#check @SerrePositivity.KST.SConstruction.relativeKanOuterSpanComposite
#print axioms SerrePositivity.KST.SConstruction.relativeKanOuterSpanComposite

#check @SerrePositivity.KST.SConstruction.relativeKanOuterSpanComposite_boundary
#print axioms SerrePositivity.KST.SConstruction.relativeKanOuterSpanComposite_boundary

#check @SerrePositivity.KST.SConstruction.relativeKanOuterSpanComposite_boundary_constant
#print axioms SerrePositivity.KST.SConstruction.relativeKanOuterSpanComposite_boundary_constant

#check @SerrePositivity.KST.SConstruction.coincidentKanSpanBoundaryData
#print axioms SerrePositivity.KST.SConstruction.coincidentKanSpanBoundaryData

#check @SerrePositivity.KST.SConstruction.coincidentKanHomotopySpanEdge
#print axioms SerrePositivity.KST.SConstruction.coincidentKanHomotopySpanEdge

#check @SerrePositivity.KST.SConstruction.coincidentKanHomotopySpanBoundary
#print axioms SerrePositivity.KST.SConstruction.coincidentKanHomotopySpanBoundary

#check @SerrePositivity.KST.SConstruction.relativeKanCoincidentSpanComposite
#print axioms SerrePositivity.KST.SConstruction.relativeKanCoincidentSpanComposite

#check @SerrePositivity.KST.SConstruction.relativeKanCoincidentSpanComposite_boundary
#print axioms SerrePositivity.KST.SConstruction.relativeKanCoincidentSpanComposite_boundary

#check @SerrePositivity.KST.SConstruction.relativeSequenceCoincidentSpanHomotopy
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceCoincidentSpanHomotopy

#check @SerrePositivity.KST.SConstruction.relativeSequenceCoincidentSpanHomotopy_boundary
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceCoincidentSpanHomotopy_boundary

#check @SerrePositivity.KST.SConstruction.relativeSequenceCoincidentSpanRectification
#print axioms SerrePositivity.KST.SConstruction.relativeSequenceCoincidentSpanRectification

#check @SerrePositivity.KST.SConstruction.relativeKCoincidentSpanFamilyRectificationData
#print axioms SerrePositivity.KST.SConstruction.relativeKCoincidentSpanFamilyRectificationData

#check @SerrePositivity.KST.SConstruction.relativeKCoincidentSpanFamilyRectificationData_boundary
#print axioms SerrePositivity.KST.SConstruction.relativeKCoincidentSpanFamilyRectificationData_boundary

#check @SerrePositivity.KST.SConstruction.relativeKCoincidentSpanFamilyRectificationData_projection
#print axioms SerrePositivity.KST.SConstruction.relativeKCoincidentSpanFamilyRectificationData_projection

#check @SerrePositivity.KST.SConstruction.relativeKanOuterSpanTriangle
#print axioms SerrePositivity.KST.SConstruction.relativeKanOuterSpanTriangle

#check @SerrePositivity.KST.SConstruction.relativeKanOuterSpanTriangleFamily
#print axioms SerrePositivity.KST.SConstruction.relativeKanOuterSpanTriangleFamily

#check @SerrePositivity.KST.SConstruction.relativeKanOuterSpanTriangleFamily_boundary
#print axioms SerrePositivity.KST.SConstruction.relativeKanOuterSpanTriangleFamily_boundary

#check @SerrePositivity.KST.SConstruction.relativeKanOuterSpanTriangleFamily_source
#print axioms SerrePositivity.KST.SConstruction.relativeKanOuterSpanTriangleFamily_source

#check @SerrePositivity.KST.SConstruction.relativeKanOuterSpanTriangleFamily_target
#print axioms SerrePositivity.KST.SConstruction.relativeKanOuterSpanTriangleFamily_target

#check @SerrePositivity.KST.SConstruction.relativeKanOuterSpanTriangleFamily_composite
#print axioms SerrePositivity.KST.SConstruction.relativeKanOuterSpanTriangleFamily_composite

#check @SerrePositivity.KST.SConstruction.coherentStringEndpointMap
#print axioms SerrePositivity.KST.SConstruction.coherentStringEndpointMap

#check @SerrePositivity.KST.SConstruction.coherentStringEndpointMap_first
#print axioms SerrePositivity.KST.SConstruction.coherentStringEndpointMap_first

#check @SerrePositivity.KST.SConstruction.coherentStringEndpointMap_last
#print axioms SerrePositivity.KST.SConstruction.coherentStringEndpointMap_last

#check @SerrePositivity.KST.SConstruction.coherentStringEndpointMap_one
#print axioms SerrePositivity.KST.SConstruction.coherentStringEndpointMap_one

#check @SerrePositivity.KST.SConstruction.coherentStringEndpointMap_comp
#print axioms SerrePositivity.KST.SConstruction.coherentStringEndpointMap_comp

#check @SerrePositivity.KST.SConstruction.CoherentArrowString
#print axioms SerrePositivity.KST.SConstruction.CoherentArrowString

#check @SerrePositivity.KST.SConstruction.CoherentArrowStringHom
#print axioms SerrePositivity.KST.SConstruction.CoherentArrowStringHom

#check @SerrePositivity.KST.SConstruction.CoherentArrowStringHom.ext
#print axioms SerrePositivity.KST.SConstruction.CoherentArrowStringHom.ext

#check @SerrePositivity.KST.SConstruction.coherentArrowString_category
#print axioms SerrePositivity.KST.SConstruction.coherentArrowString_category

#check @SerrePositivity.KST.SConstruction.coherentArrowString_first
#print axioms SerrePositivity.KST.SConstruction.coherentArrowString_first

#check @SerrePositivity.KST.SConstruction.coherentArrowString_last
#print axioms SerrePositivity.KST.SConstruction.coherentArrowString_last

#check @SerrePositivity.KST.SConstruction.coherentArrowStringDirect
#print axioms SerrePositivity.KST.SConstruction.coherentArrowStringDirect

#check @SerrePositivity.KST.SConstruction.coherentArrowStringDirectTo
#print axioms SerrePositivity.KST.SConstruction.coherentArrowStringDirectTo

#check @SerrePositivity.KST.SConstruction.coherentArrowStringDirectTo_unique
#print axioms SerrePositivity.KST.SConstruction.coherentArrowStringDirectTo_unique

#check @SerrePositivity.KST.SConstruction.coherentArrowStringDirect_isInitial
#print axioms SerrePositivity.KST.SConstruction.coherentArrowStringDirect_isInitial

#check @SerrePositivity.KST.SConstruction.coherentArrowStringContractionTransformation
#print axioms SerrePositivity.KST.SConstruction.coherentArrowStringContractionTransformation

#check @SerrePositivity.KST.SConstruction.coherentArrowStringConstant_nerve
#print axioms SerrePositivity.KST.SConstruction.coherentArrowStringConstant_nerve

#check @SerrePositivity.KST.SConstruction.coherentArrowStringContraction
#print axioms SerrePositivity.KST.SConstruction.coherentArrowStringContraction

#check @SerrePositivity.KST.SConstruction.coherentStringRefinementPath
#print axioms SerrePositivity.KST.SConstruction.coherentStringRefinementPath

#check @SerrePositivity.KST.SConstruction.coherentStringPathReindex
#print axioms SerrePositivity.KST.SConstruction.coherentStringPathReindex

#check @SerrePositivity.KST.SConstruction.coherentStringPathReindexFunctor
#print axioms SerrePositivity.KST.SConstruction.coherentStringPathReindexFunctor

#check @SerrePositivity.KST.SConstruction.coherentStringRefinementPath_comp
#print axioms SerrePositivity.KST.SConstruction.coherentStringRefinementPath_comp

#check @SerrePositivity.KST.SConstruction.coherentStringRefinementPathInclusion
#print axioms SerrePositivity.KST.SConstruction.coherentStringRefinementPathInclusion

#check @SerrePositivity.KST.SConstruction.coherentStringPathFlag
#print axioms SerrePositivity.KST.SConstruction.coherentStringPathFlag

#check @SerrePositivity.KST.SConstruction.coherentStringPathFlag_naturality
#print axioms SerrePositivity.KST.SConstruction.coherentStringPathFlag_naturality

#check @SerrePositivity.KST.SConstruction.coherentStringVertexObject
#print axioms SerrePositivity.KST.SConstruction.coherentStringVertexObject

#check @SerrePositivity.KST.SConstruction.coherentStringCell_object
#print axioms SerrePositivity.KST.SConstruction.coherentStringCell_object

#check @SerrePositivity.KST.SConstruction.coherentStringDiagramCell
#print axioms SerrePositivity.KST.SConstruction.coherentStringDiagramCell

#check @SerrePositivity.KST.SConstruction.coherentString_reobject_precomp
#print axioms SerrePositivity.KST.SConstruction.coherentString_reobject_precomp

#check @SerrePositivity.KST.SConstruction.coherentStringDiagramCell_naturality
#print axioms SerrePositivity.KST.SConstruction.coherentStringDiagramCell_naturality

#check @SerrePositivity.KST.SConstruction.CoherentArrowString.mk
#print axioms SerrePositivity.KST.SConstruction.CoherentArrowString.mk

#check @SerrePositivity.KST.SConstruction.CoherentArrowString.length
#print axioms SerrePositivity.KST.SConstruction.CoherentArrowString.length

#check @SerrePositivity.KST.SConstruction.CoherentArrowString.chain
#print axioms SerrePositivity.KST.SConstruction.CoherentArrowString.chain

#check @SerrePositivity.KST.SConstruction.CoherentArrowString.long_edge
#print axioms SerrePositivity.KST.SConstruction.CoherentArrowString.long_edge

#check @SerrePositivity.KST.SConstruction.CoherentArrowStringHom.mk
#print axioms SerrePositivity.KST.SConstruction.CoherentArrowStringHom.mk

#check @SerrePositivity.KST.SConstruction.CoherentArrowStringHom.map
#print axioms SerrePositivity.KST.SConstruction.CoherentArrowStringHom.map

#check @SerrePositivity.KST.SConstruction.CoherentArrowStringHom.first
#print axioms SerrePositivity.KST.SConstruction.CoherentArrowStringHom.first

#check @SerrePositivity.KST.SConstruction.CoherentArrowStringHom.last
#print axioms SerrePositivity.KST.SConstruction.CoherentArrowStringHom.last

#check @SerrePositivity.KST.SConstruction.CoherentArrowStringHom.comm
#print axioms SerrePositivity.KST.SConstruction.CoherentArrowStringHom.comm

#check @SerrePositivity.KST.SConstruction.coherentPathImageFunctor
#print axioms SerrePositivity.KST.SConstruction.coherentPathImageFunctor

#check @SerrePositivity.KST.SConstruction.coherentPathImageFunctor_nerve_heq
#print axioms SerrePositivity.KST.SConstruction.coherentPathImageFunctor_nerve_heq

#check @SerrePositivity.KST.SConstruction.coherentStringPathReindexFunctor_native_heq
#print axioms SerrePositivity.KST.SConstruction.coherentStringPathReindexFunctor_native_heq

#check @SerrePositivity.KST.SConstruction.coherentStringNativeMap
#print axioms SerrePositivity.KST.SConstruction.coherentStringNativeMap

#check @SerrePositivity.KST.SConstruction.coherentStringNativeMap_heq
#print axioms SerrePositivity.KST.SConstruction.coherentStringNativeMap_heq

#check @SerrePositivity.KST.SConstruction.coherentString_enrichedMap_objects_heq
#print axioms SerrePositivity.KST.SConstruction.coherentString_enrichedMap_objects_heq

#check @SerrePositivity.KST.SConstruction.coherentStringNativeMap_naturality
#print axioms SerrePositivity.KST.SConstruction.coherentStringNativeMap_naturality

#check @SerrePositivity.KST.SConstruction.coherentStringFullPath
#print axioms SerrePositivity.KST.SConstruction.coherentStringFullPath

#check @SerrePositivity.KST.SConstruction.coherentStringRefinementPath_id
#print axioms SerrePositivity.KST.SConstruction.coherentStringRefinementPath_id

#check @SerrePositivity.KST.SConstruction.coherentStringRefinementPath_directTo
#print axioms SerrePositivity.KST.SConstruction.coherentStringRefinementPath_directTo

#check @SerrePositivity.KST.SConstruction.coherentStringPathFlag_vertex
#print axioms SerrePositivity.KST.SConstruction.coherentStringPathFlag_vertex

#check @SerrePositivity.KST.SConstruction.coherentStringFullPath_direct
#print axioms SerrePositivity.KST.SConstruction.coherentStringFullPath_direct

#check @SerrePositivity.KST.SConstruction.coherentArrowNativeFamily
#print axioms SerrePositivity.KST.SConstruction.coherentArrowNativeFamily

#check @SerrePositivity.KST.SConstruction.coherentArrowNativeInitialVertex
#print axioms SerrePositivity.KST.SConstruction.coherentArrowNativeInitialVertex

#check @SerrePositivity.KST.SConstruction.coherentArrowNativeContraction
#print axioms SerrePositivity.KST.SConstruction.coherentArrowNativeContraction

#check @SerrePositivity.KST.SConstruction.coherentArrowNativeFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.coherentArrowNativeFamily_vertex

#check @SerrePositivity.KST.SConstruction.coherentArrowNativeInitialVertex_endpoint
#print axioms SerrePositivity.KST.SConstruction.coherentArrowNativeInitialVertex_endpoint

#check @SerrePositivity.KST.SConstruction.coherentOrdinaryPrismForward
#print axioms SerrePositivity.KST.SConstruction.coherentOrdinaryPrismForward

#check @SerrePositivity.KST.SConstruction.coherentOrdinaryPrismBackward
#print axioms SerrePositivity.KST.SConstruction.coherentOrdinaryPrismBackward

#check @SerrePositivity.KST.SConstruction.coherentOrdinaryPrism_forward_backward
#print axioms SerrePositivity.KST.SConstruction.coherentOrdinaryPrism_forward_backward

#check @SerrePositivity.KST.SConstruction.coherentOrdinaryPrism_backward_forward
#print axioms SerrePositivity.KST.SConstruction.coherentOrdinaryPrism_backward_forward

#check @SerrePositivity.KST.SConstruction.coherentOrdinaryPrismIso
#print axioms SerrePositivity.KST.SConstruction.coherentOrdinaryPrismIso

#check @SerrePositivity.KST.SConstruction.kPrismNativeStringFamilies_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kPrismNativeStringFamilies_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismStringDiagram
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismStringDiagram

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismStringDiagram_recover
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismStringDiagram_recover

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismStringDiagram_simplex
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismStringDiagram_simplex

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismNativeFamily
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismNativeFamily

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismNativeContraction
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismNativeContraction

#check @SerrePositivity.KST.SConstruction.coherentLowerStringIndex
#print axioms SerrePositivity.KST.SConstruction.coherentLowerStringIndex

#check @SerrePositivity.KST.SConstruction.coherentUpperStringIndex
#print axioms SerrePositivity.KST.SConstruction.coherentUpperStringIndex

#check @SerrePositivity.KST.SConstruction.coherentLowerStringTime
#print axioms SerrePositivity.KST.SConstruction.coherentLowerStringTime

#check @SerrePositivity.KST.SConstruction.coherentUpperStringTime
#print axioms SerrePositivity.KST.SConstruction.coherentUpperStringTime

#check @SerrePositivity.KST.SConstruction.coherentLowerStringExtend
#print axioms SerrePositivity.KST.SConstruction.coherentLowerStringExtend

#check @SerrePositivity.KST.SConstruction.coherentUpperStringExtend
#print axioms SerrePositivity.KST.SConstruction.coherentUpperStringExtend

#check @SerrePositivity.KST.SConstruction.coherentLowerStringExtend_castSucc
#print axioms SerrePositivity.KST.SConstruction.coherentLowerStringExtend_castSucc

#check @SerrePositivity.KST.SConstruction.coherentLowerStringExtend_last
#print axioms SerrePositivity.KST.SConstruction.coherentLowerStringExtend_last

#check @SerrePositivity.KST.SConstruction.coherentUpperStringExtend_zero
#print axioms SerrePositivity.KST.SConstruction.coherentUpperStringExtend_zero

#check @SerrePositivity.KST.SConstruction.coherentUpperStringExtend_succ
#print axioms SerrePositivity.KST.SConstruction.coherentUpperStringExtend_succ

#check @SerrePositivity.KST.SConstruction.coherentLowerStringExtend_index
#print axioms SerrePositivity.KST.SConstruction.coherentLowerStringExtend_index

#check @SerrePositivity.KST.SConstruction.coherentUpperStringExtend_index
#print axioms SerrePositivity.KST.SConstruction.coherentUpperStringExtend_index

#check @SerrePositivity.KST.SConstruction.coherentLowerStringExtend_time
#print axioms SerrePositivity.KST.SConstruction.coherentLowerStringExtend_time

#check @SerrePositivity.KST.SConstruction.coherentUpperStringExtend_time
#print axioms SerrePositivity.KST.SConstruction.coherentUpperStringExtend_time

#check @SerrePositivity.KST.SConstruction.coherentLowerStringIndex_first
#print axioms SerrePositivity.KST.SConstruction.coherentLowerStringIndex_first

#check @SerrePositivity.KST.SConstruction.coherentLowerStringIndex_last
#print axioms SerrePositivity.KST.SConstruction.coherentLowerStringIndex_last

#check @SerrePositivity.KST.SConstruction.coherentLowerStringTime_first
#print axioms SerrePositivity.KST.SConstruction.coherentLowerStringTime_first

#check @SerrePositivity.KST.SConstruction.coherentLowerStringTime_last
#print axioms SerrePositivity.KST.SConstruction.coherentLowerStringTime_last

#check @SerrePositivity.KST.SConstruction.coherentLowerStringExtend_id
#print axioms SerrePositivity.KST.SConstruction.coherentLowerStringExtend_id

#check @SerrePositivity.KST.SConstruction.coherentLowerStringExtend_comp
#print axioms SerrePositivity.KST.SConstruction.coherentLowerStringExtend_comp

#check @SerrePositivity.KST.SConstruction.coherentUpperStringIndex_first
#print axioms SerrePositivity.KST.SConstruction.coherentUpperStringIndex_first

#check @SerrePositivity.KST.SConstruction.coherentUpperStringIndex_last
#print axioms SerrePositivity.KST.SConstruction.coherentUpperStringIndex_last

#check @SerrePositivity.KST.SConstruction.coherentUpperStringTime_first
#print axioms SerrePositivity.KST.SConstruction.coherentUpperStringTime_first

#check @SerrePositivity.KST.SConstruction.coherentUpperStringTime_last
#print axioms SerrePositivity.KST.SConstruction.coherentUpperStringTime_last

#check @SerrePositivity.KST.SConstruction.coherentUpperStringExtend_id
#print axioms SerrePositivity.KST.SConstruction.coherentUpperStringExtend_id

#check @SerrePositivity.KST.SConstruction.coherentUpperStringExtend_comp
#print axioms SerrePositivity.KST.SConstruction.coherentUpperStringExtend_comp

#check @SerrePositivity.KST.SConstruction.coherentLowerStringExtend_first
#print axioms SerrePositivity.KST.SConstruction.coherentLowerStringExtend_first

#check @SerrePositivity.KST.SConstruction.coherentUpperStringExtend_last
#print axioms SerrePositivity.KST.SConstruction.coherentUpperStringExtend_last

#check @SerrePositivity.KST.SConstruction.coherentStringPrismChain
#print axioms SerrePositivity.KST.SConstruction.coherentStringPrismChain

#check @SerrePositivity.KST.SConstruction.coherentStringPrismChain_reindex
#print axioms SerrePositivity.KST.SConstruction.coherentStringPrismChain_reindex

#check @SerrePositivity.KST.SConstruction.coherentStringPrismChain_longEdge
#print axioms SerrePositivity.KST.SConstruction.coherentStringPrismChain_longEdge

#check @SerrePositivity.KST.SConstruction.coherentStringPrismChain_refinement
#print axioms SerrePositivity.KST.SConstruction.coherentStringPrismChain_refinement

#check @SerrePositivity.KST.SConstruction.coherentLowerPrismString
#print axioms SerrePositivity.KST.SConstruction.coherentLowerPrismString

#check @SerrePositivity.KST.SConstruction.coherentLowerPrismStringMap
#print axioms SerrePositivity.KST.SConstruction.coherentLowerPrismStringMap

#check @SerrePositivity.KST.SConstruction.coherentLowerPrismStringFunctor
#print axioms SerrePositivity.KST.SConstruction.coherentLowerPrismStringFunctor

#check @SerrePositivity.KST.SConstruction.coherentUpperPrismString
#print axioms SerrePositivity.KST.SConstruction.coherentUpperPrismString

#check @SerrePositivity.KST.SConstruction.coherentUpperPrismStringMap
#print axioms SerrePositivity.KST.SConstruction.coherentUpperPrismStringMap

#check @SerrePositivity.KST.SConstruction.coherentUpperPrismStringFunctor
#print axioms SerrePositivity.KST.SConstruction.coherentUpperPrismStringFunctor

#check @SerrePositivity.KST.SConstruction.coherentPrismArrow
#print axioms SerrePositivity.KST.SConstruction.coherentPrismArrow

#check @SerrePositivity.KST.SConstruction.coherentPrismLowerNativeFamily
#print axioms SerrePositivity.KST.SConstruction.coherentPrismLowerNativeFamily

#check @SerrePositivity.KST.SConstruction.coherentPrismLowerNativeContraction
#print axioms SerrePositivity.KST.SConstruction.coherentPrismLowerNativeContraction

#check @SerrePositivity.KST.SConstruction.coherentPrismLowerNativeContraction_h
#print axioms SerrePositivity.KST.SConstruction.coherentPrismLowerNativeContraction_h

#check @SerrePositivity.KST.SConstruction.coherentPrismLowerNativeFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.coherentPrismLowerNativeFamily_vertex

#check @SerrePositivity.KST.SConstruction.coherentPrismUpperNativeFamily
#print axioms SerrePositivity.KST.SConstruction.coherentPrismUpperNativeFamily

#check @SerrePositivity.KST.SConstruction.coherentPrismUpperNativeContraction
#print axioms SerrePositivity.KST.SConstruction.coherentPrismUpperNativeContraction

#check @SerrePositivity.KST.SConstruction.coherentPrismUpperNativeContraction_h
#print axioms SerrePositivity.KST.SConstruction.coherentPrismUpperNativeContraction_h

#check @SerrePositivity.KST.SConstruction.coherentPrismUpperNativeFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.coherentPrismUpperNativeFamily_vertex

#check @SerrePositivity.KST.SConstruction.kPrismNativeSpanFamilies_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kPrismNativeSpanFamilies_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerNativeFamily
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerNativeFamily

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerNativeContraction
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerNativeContraction

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerNativeContraction_h
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerNativeContraction_h

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperNativeFamily
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperNativeFamily

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperNativeContraction
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperNativeContraction

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperNativeContraction_h
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperNativeContraction_h

#check @SerrePositivity.KST.SConstruction.coherentPrismSliceFunctor
#print axioms SerrePositivity.KST.SConstruction.coherentPrismSliceFunctor

#check @SerrePositivity.KST.SConstruction.coherentOrdinaryPrismSlice_zero
#print axioms SerrePositivity.KST.SConstruction.coherentOrdinaryPrismSlice_zero

#check @SerrePositivity.KST.SConstruction.coherentOrdinaryPrismSlice_one
#print axioms SerrePositivity.KST.SConstruction.coherentOrdinaryPrismSlice_one

#check @SerrePositivity.KST.SConstruction.coherentOrdinaryPrismSlice_source
#print axioms SerrePositivity.KST.SConstruction.coherentOrdinaryPrismSlice_source

#check @SerrePositivity.KST.SConstruction.coherentOrdinaryPrismSlice_target
#print axioms SerrePositivity.KST.SConstruction.coherentOrdinaryPrismSlice_target

#check @SerrePositivity.KST.SConstruction.coherentStringVertexObject_precomp
#print axioms SerrePositivity.KST.SConstruction.coherentStringVertexObject_precomp

#check @SerrePositivity.KST.SConstruction.kPrismSliceDiagrams_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kPrismSliceDiagrams_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismStringDiagram_bottom
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismStringDiagram_bottom

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismStringDiagram_top
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismStringDiagram_top

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismStringVertex_bottom
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismStringVertex_bottom

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismStringVertex_top
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismStringVertex_top

#check @SerrePositivity.KST.SConstruction.kPrismSliceEdges_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kPrismSliceEdges_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismStringEdge_bottom
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismStringEdge_bottom

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismStringEdge_top
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismStringEdge_top

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismStringEdge_vertical
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismStringEdge_vertical

#check @SerrePositivity.KST.SConstruction.coherentLowerPrismRefinementPath_cut
#print axioms SerrePositivity.KST.SConstruction.coherentLowerPrismRefinementPath_cut

#check @SerrePositivity.KST.SConstruction.coherentUpperPrismRefinementPath_cut
#print axioms SerrePositivity.KST.SConstruction.coherentUpperPrismRefinementPath_cut

#check @SerrePositivity.KST.SConstruction.coherentLowerPrismPathFlag_through
#print axioms SerrePositivity.KST.SConstruction.coherentLowerPrismPathFlag_through

#check @SerrePositivity.KST.SConstruction.coherentUpperPrismPathFlag_through
#print axioms SerrePositivity.KST.SConstruction.coherentUpperPrismPathFlag_through

#check @SerrePositivity.KST.SConstruction.coherentPathFlag_mapping_comp
#print axioms SerrePositivity.KST.SConstruction.coherentPathFlag_mapping_comp

#check @SerrePositivity.KST.SConstruction.coherentLowerPrismPathFlag_mapping_comp
#print axioms SerrePositivity.KST.SConstruction.coherentLowerPrismPathFlag_mapping_comp

#check @SerrePositivity.KST.SConstruction.coherentUpperPrismPathFlag_mapping_comp
#print axioms SerrePositivity.KST.SConstruction.coherentUpperPrismPathFlag_mapping_comp

#check @SerrePositivity.KST.SConstruction.kPrismNativeSpanTargets_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kPrismNativeSpanTargets_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalSuspensionMappingTarget
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalSuspensionMappingTarget

#check @SerrePositivity.KST.SConstruction.kKanOriginalSuspensionMappingTarget_kanComplex
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalSuspensionMappingTarget_kanComplex

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismNativeHomIso
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismNativeHomIso

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismSpanInitialVertex
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismSpanInitialVertex

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerSuspensionFamily
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerSuspensionFamily

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerSuspensionContraction
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerSuspensionContraction

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerSuspensionFamily_recover
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerSuspensionFamily_recover

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerSuspensionContraction_recover
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerSuspensionContraction_recover

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperSuspensionFamily
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperSuspensionFamily

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperSuspensionContraction
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperSuspensionContraction

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperSuspensionFamily_recover
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperSuspensionFamily_recover

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperSuspensionContraction_recover
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperSuspensionContraction_recover

#check @SerrePositivity.KST.SConstruction.coherentStringDiagramCell_strict_map
#print axioms SerrePositivity.KST.SConstruction.coherentStringDiagramCell_strict_map

#check @SerrePositivity.KST.SConstruction.coherentLastPathFace_epi
#print axioms SerrePositivity.KST.SConstruction.coherentLastPathFace_epi

#check @SerrePositivity.KST.SConstruction.coherentFirstPathFace_epi
#print axioms SerrePositivity.KST.SConstruction.coherentFirstPathFace_epi

#check @SerrePositivity.KST.SConstruction.coherentLowerStringFace_index
#print axioms SerrePositivity.KST.SConstruction.coherentLowerStringFace_index

#check @SerrePositivity.KST.SConstruction.coherentLowerStringFace_time
#print axioms SerrePositivity.KST.SConstruction.coherentLowerStringFace_time

#check @SerrePositivity.KST.SConstruction.coherentUpperStringFace_index
#print axioms SerrePositivity.KST.SConstruction.coherentUpperStringFace_index

#check @SerrePositivity.KST.SConstruction.coherentUpperStringFace_time
#print axioms SerrePositivity.KST.SConstruction.coherentUpperStringFace_time

#check @SerrePositivity.KST.SConstruction.coherentLowerPrismString_horizontalFace
#print axioms SerrePositivity.KST.SConstruction.coherentLowerPrismString_horizontalFace

#check @SerrePositivity.KST.SConstruction.coherentUpperPrismString_horizontalFace
#print axioms SerrePositivity.KST.SConstruction.coherentUpperPrismString_horizontalFace

#check @SerrePositivity.KST.SConstruction.coherentLowerPrismString_rawHorizontalCell
#print axioms SerrePositivity.KST.SConstruction.coherentLowerPrismString_rawHorizontalCell

#check @SerrePositivity.KST.SConstruction.coherentUpperPrismString_rawHorizontalCell
#print axioms SerrePositivity.KST.SConstruction.coherentUpperPrismString_rawHorizontalCell

#check @SerrePositivity.KST.SConstruction.coherentPathActionsConstant
#print axioms SerrePositivity.KST.SConstruction.coherentPathActionsConstant

#check @SerrePositivity.KST.SConstruction.coherentStrictDiagramPathActionsConstant
#print axioms SerrePositivity.KST.SConstruction.coherentStrictDiagramPathActionsConstant

#check @SerrePositivity.KST.SConstruction.coherentPathValues_eq_of_epi
#print axioms SerrePositivity.KST.SConstruction.coherentPathValues_eq_of_epi

#check @SerrePositivity.KST.SConstruction.coherentPathMap_eq_const
#print axioms SerrePositivity.KST.SConstruction.coherentPathMap_eq_const

#check @SerrePositivity.KST.SConstruction.coherentAdjacentPath_mem
#print axioms SerrePositivity.KST.SConstruction.coherentAdjacentPath_mem

#check @SerrePositivity.KST.SConstruction.coherentAdjacentPath_subsingleton
#print axioms SerrePositivity.KST.SConstruction.coherentAdjacentPath_subsingleton

#check @SerrePositivity.KST.SConstruction.coherentAdjacentPathValues_eq
#print axioms SerrePositivity.KST.SConstruction.coherentAdjacentPathValues_eq

#check @SerrePositivity.KST.SConstruction.coherentAdjacentPathMap_eq_const
#print axioms SerrePositivity.KST.SConstruction.coherentAdjacentPathMap_eq_const

#check @SerrePositivity.KST.SConstruction.kPrismHorizontalPathEvaluation_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kPrismHorizontalPathEvaluation_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerHorizontalValues_eq
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerHorizontalValues_eq

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperHorizontalValues_eq
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperHorizontalValues_eq

#check @SerrePositivity.KST.SConstruction.coherentCompositionFaceValues_eq
#print axioms SerrePositivity.KST.SConstruction.coherentCompositionFaceValues_eq

#check @SerrePositivity.KST.SConstruction.coherentCompositionFaceMap_eq_const
#print axioms SerrePositivity.KST.SConstruction.coherentCompositionFaceMap_eq_const

#check @SerrePositivity.KST.SConstruction.kPrismCompositionFaceValues_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kPrismCompositionFaceValues_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerCompositionValues_eq
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerCompositionValues_eq

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperCompositionValues_eq
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperCompositionValues_eq

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerNativeValues_eq
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerNativeValues_eq

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperNativeValues_eq
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperNativeValues_eq

#check @SerrePositivity.KST.SConstruction.coherentStringPathReindex_fullPath
#print axioms SerrePositivity.KST.SConstruction.coherentStringPathReindex_fullPath

#check @SerrePositivity.KST.SConstruction.coherentStringNativeMap_refinementVertex
#print axioms SerrePositivity.KST.SConstruction.coherentStringNativeMap_refinementVertex

#check @SerrePositivity.KST.SConstruction.kPrismSpanEndpointsConstant_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kPrismSpanEndpointsConstant_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerNativeFamily_eq_const
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerNativeFamily_eq_const

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperNativeFamily_eq_const
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperNativeFamily_eq_const

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerSuspensionFamily_eq_const
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerSuspensionFamily_eq_const

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerEndpointVertex
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerEndpointVertex

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerEndpointContraction
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerEndpointContraction

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerEndpointContraction_h
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerEndpointContraction_h

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperSuspensionFamily_eq_const
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperSuspensionFamily_eq_const

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperEndpointVertex
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperEndpointVertex

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperEndpointContraction
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperEndpointContraction

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperEndpointContraction_h
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperEndpointContraction_h

#check @SerrePositivity.KST.SConstruction.coherentTrianglePath_eq_composite
#print axioms SerrePositivity.KST.SConstruction.coherentTrianglePath_eq_composite

#check @SerrePositivity.KST.SConstruction.coherentTrianglePath_composite_value
#print axioms SerrePositivity.KST.SConstruction.coherentTrianglePath_composite_value

#check @SerrePositivity.KST.SConstruction.coherentTrianglePath_specified_composite_heq
#print axioms SerrePositivity.KST.SConstruction.coherentTrianglePath_specified_composite_heq

#check @SerrePositivity.KST.SConstruction.coherentTrianglePath_value_heq
#print axioms SerrePositivity.KST.SConstruction.coherentTrianglePath_value_heq

#check @SerrePositivity.KST.SConstruction.coherentEqToHom_value_heq
#print axioms SerrePositivity.KST.SConstruction.coherentEqToHom_value_heq

#check @SerrePositivity.KST.SConstruction.coherentStringNativeMap_value_heq
#print axioms SerrePositivity.KST.SConstruction.coherentStringNativeMap_value_heq

#check @SerrePositivity.KST.SConstruction.coherentLowerPrismDirect_forward
#print axioms SerrePositivity.KST.SConstruction.coherentLowerPrismDirect_forward

#check @SerrePositivity.KST.SConstruction.coherentUpperPrismDirect_forward
#print axioms SerrePositivity.KST.SConstruction.coherentUpperPrismDirect_forward

#check @SerrePositivity.KST.SConstruction.coherentStringRefinementPathToFull
#print axioms SerrePositivity.KST.SConstruction.coherentStringRefinementPathToFull

#check @SerrePositivity.KST.SConstruction.coherentStringPathFlag_arrow
#print axioms SerrePositivity.KST.SConstruction.coherentStringPathFlag_arrow

#check @SerrePositivity.KST.SConstruction.coherentArrowNativeContraction_vertex_edge
#print axioms SerrePositivity.KST.SConstruction.coherentArrowNativeContraction_vertex_edge

#check @SerrePositivity.KST.SConstruction.coherentHomotopyVertexEdge_precomp
#print axioms SerrePositivity.KST.SConstruction.coherentHomotopyVertexEdge_precomp

#check @SerrePositivity.KST.SConstruction.coherentArrowNativeContraction_prepost_vertex_edge
#print axioms SerrePositivity.KST.SConstruction.coherentArrowNativeContraction_prepost_vertex_edge

#check @SerrePositivity.KST.SConstruction.kPrismEndpointComposites_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kPrismEndpointComposites_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerDirect_cell
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerDirect_cell

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerEndpointVertex_raw_heq
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerEndpointVertex_raw_heq

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperDirect_cell
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperDirect_cell

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperEndpointVertex_raw_heq
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperEndpointVertex_raw_heq

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerEndpointVertex_composite
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerEndpointVertex_composite

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperEndpointVertex_composite
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperEndpointVertex_composite

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerSuspensionFamily_composite
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerSuspensionFamily_composite

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerCompositeContraction
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerCompositeContraction

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerCompositeContraction_h
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerCompositeContraction_h

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperSuspensionFamily_composite
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperSuspensionFamily_composite

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperCompositeContraction
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperCompositeContraction

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperCompositeContraction_h
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperCompositeContraction_h

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerCompositeContraction_vertex_edge
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerCompositeContraction_vertex_edge

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperCompositeContraction_vertex_edge
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperCompositeContraction_vertex_edge

#check @SerrePositivity.KST.SConstruction.coherentTriangleMappingEdge_raw_heq
#print axioms SerrePositivity.KST.SConstruction.coherentTriangleMappingEdge_raw_heq

#check @SerrePositivity.KST.SConstruction.coherentTriangleEdgeValue_heq
#print axioms SerrePositivity.KST.SConstruction.coherentTriangleEdgeValue_heq

#check @SerrePositivity.KST.SConstruction.coherentStringRefinementPathToFull_triangle_heq
#print axioms SerrePositivity.KST.SConstruction.coherentStringRefinementPathToFull_triangle_heq

#check @SerrePositivity.KST.SConstruction.kPrismBoundaryLegs_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kPrismBoundaryLegs_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismNativeHomIso_value_heq
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismNativeHomIso_value_heq

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerCompositeContraction_boundary_leg
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismLowerCompositeContraction_boundary_leg

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperCompositeContraction_boundary_leg
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismUpperCompositeContraction_boundary_leg

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismSpanInitialVertex_diagonal
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismSpanInitialVertex_diagonal

#check @SerrePositivity.KST.SConstruction.specifiedParameterPoint_mono
#print axioms SerrePositivity.KST.SConstruction.specifiedParameterPoint_mono

#check @SerrePositivity.KST.SConstruction.specifiedPointRestriction_edge
#print axioms SerrePositivity.KST.SConstruction.specifiedPointRestriction_edge

#check @SerrePositivity.KST.SConstruction.specifiedPointSpanEdge
#print axioms SerrePositivity.KST.SConstruction.specifiedPointSpanEdge

#check @SerrePositivity.KST.SConstruction.specifiedPointSpanTriangle
#print axioms SerrePositivity.KST.SConstruction.specifiedPointSpanTriangle

#check @SerrePositivity.KST.SConstruction.specifiedPointSimplex_uncurry
#print axioms SerrePositivity.KST.SConstruction.specifiedPointSimplex_uncurry

#check @SerrePositivity.KST.SConstruction.specifiedPointSpanComposite
#print axioms SerrePositivity.KST.SConstruction.specifiedPointSpanComposite

#check @SerrePositivity.KST.SConstruction.specifiedPointSpanComposite_boundary
#print axioms SerrePositivity.KST.SConstruction.specifiedPointSpanComposite_boundary

#check @SerrePositivity.KST.SConstruction.specifiedPointSpanTriangleFamily
#print axioms SerrePositivity.KST.SConstruction.specifiedPointSpanTriangleFamily

#check @SerrePositivity.KST.SConstruction.specifiedPointSpanTriangleFamily_boundary
#print axioms SerrePositivity.KST.SConstruction.specifiedPointSpanTriangleFamily_boundary

#check @SerrePositivity.KST.SConstruction.specifiedPointSpanTriangleFamily_source
#print axioms SerrePositivity.KST.SConstruction.specifiedPointSpanTriangleFamily_source

#check @SerrePositivity.KST.SConstruction.specifiedPointSpanTriangleFamily_target
#print axioms SerrePositivity.KST.SConstruction.specifiedPointSpanTriangleFamily_target

#check @SerrePositivity.KST.SConstruction.specifiedPointSpanTriangleFamily_composite
#print axioms SerrePositivity.KST.SConstruction.specifiedPointSpanTriangleFamily_composite

#check @SerrePositivity.KST.SConstruction.kPrismSpecifiedSpanFamilies_pointed_simplicialCategory
#print axioms SerrePositivity.KST.SConstruction.kPrismSpecifiedSpanFamilies_pointed_simplicialCategory

#check @SerrePositivity.KST.SConstruction.kPrismSpecifiedSpanFamilies_native_kan
#print axioms SerrePositivity.KST.SConstruction.kPrismSpecifiedSpanFamilies_native_kan

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedOuterTriangleData
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedOuterTriangleData

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedOuterTriangleData_simplex
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedOuterTriangleData_simplex

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedCompatibilityFamily
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedCompatibilityFamily

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedCompatibilityFamily_boundary
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedCompatibilityFamily_boundary

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedTriangleFamily
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedTriangleFamily

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedTriangleFamily_boundary
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedTriangleFamily_boundary

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedTriangleFamily_upper
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedTriangleFamily_upper

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedTriangleFamily_lower
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedTriangleFamily_lower

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedTriangleFamily_compatibility
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrismSpecifiedTriangleFamily_compatibility

#check @SerrePositivity.KST.SConstruction.sequenceCompatibilityFamily_precompose
#print axioms SerrePositivity.KST.SConstruction.sequenceCompatibilityFamily_precompose

#check @SerrePositivity.KST.SConstruction.sequenceCompatibilityFamily_precompose_h
#print axioms SerrePositivity.KST.SConstruction.sequenceCompatibilityFamily_precompose_h

#check @SerrePositivity.KST.SConstruction.sequenceCompatibilityFamily_precompose_boundary
#print axioms SerrePositivity.KST.SConstruction.sequenceCompatibilityFamily_precompose_boundary

#check @SerrePositivity.KST.SConstruction.monicKPrismSpecifiedCompatibilityFamily
#print axioms SerrePositivity.KST.SConstruction.monicKPrismSpecifiedCompatibilityFamily

#check @SerrePositivity.KST.SConstruction.monicKPrismSpecifiedCompatibilityFamily_h
#print axioms SerrePositivity.KST.SConstruction.monicKPrismSpecifiedCompatibilityFamily_h

#check @SerrePositivity.KST.SConstruction.monicKPrismSpecifiedCompatibilityFamily_boundary
#print axioms SerrePositivity.KST.SConstruction.monicKPrismSpecifiedCompatibilityFamily_boundary

#check @SerrePositivity.KST.SConstruction.monicKPrismSpecifiedTriangleFamily
#print axioms SerrePositivity.KST.SConstruction.monicKPrismSpecifiedTriangleFamily

#check @SerrePositivity.KST.SConstruction.monicKPrismSpecifiedTriangleFamily_boundary
#print axioms SerrePositivity.KST.SConstruction.monicKPrismSpecifiedTriangleFamily_boundary

#check @SerrePositivity.KST.SConstruction.monicKPrismSpecifiedTriangleFamily_compatibility
#print axioms SerrePositivity.KST.SConstruction.monicKPrismSpecifiedTriangleFamily_compatibility

#check @SerrePositivity.KST.SConstruction.monicKPrismSpecifiedTriangleFamily_upper
#print axioms SerrePositivity.KST.SConstruction.monicKPrismSpecifiedTriangleFamily_upper

#check @SerrePositivity.KST.SConstruction.monicKPrismSpecifiedTriangleFamily_lower
#print axioms SerrePositivity.KST.SConstruction.monicKPrismSpecifiedTriangleFamily_lower

#check @SerrePositivity.KST.SConstruction.exists_prescribed_fibration_family_transport
#print axioms SerrePositivity.KST.SConstruction.exists_prescribed_fibration_family_transport

#check @SerrePositivity.KST.SConstruction.exists_prescribed_pointed_family_adjustment
#print axioms SerrePositivity.KST.SConstruction.exists_prescribed_pointed_family_adjustment

#check @SerrePositivity.KST.SConstruction.FamilyHomotopyChain
#print axioms SerrePositivity.KST.SConstruction.FamilyHomotopyChain

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainTrace
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainTrace

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainSourceTransport
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainSourceTransport

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainSourceTransport_trace
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainSourceTransport_trace

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainAppend
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainAppend

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainMap
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainMap

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainMap_trace
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainMap_trace

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainPrecomp
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainPrecomp

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainPrecomp_trace
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainPrecomp_trace

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainSingle
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainSingle

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainSingle_trace
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainSingle_trace

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainAppend_trace
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainAppend_trace

#check @SerrePositivity.KST.SConstruction.FamilyHomotopyChain.nil
#print axioms SerrePositivity.KST.SConstruction.FamilyHomotopyChain.nil

#check @SerrePositivity.KST.SConstruction.FamilyHomotopyChain.cons
#print axioms SerrePositivity.KST.SConstruction.FamilyHomotopyChain.cons

#check @SerrePositivity.KST.SConstruction.exists_prescribedFamilyChain_lift_with_traces
#print axioms SerrePositivity.KST.SConstruction.exists_prescribedFamilyChain_lift_with_traces

#check @SerrePositivity.KST.SConstruction.prescribedFamilyChainLiftData
#print axioms SerrePositivity.KST.SConstruction.prescribedFamilyChainLiftData

#check @SerrePositivity.KST.SConstruction.exists_prescribed_pointedFamilyChain_lift_with_traces
#print axioms SerrePositivity.KST.SConstruction.exists_prescribed_pointedFamilyChain_lift_with_traces

#check @SerrePositivity.KST.SConstruction.rawSequenceStep_familyVertex
#print axioms SerrePositivity.KST.SConstruction.rawSequenceStep_familyVertex

#check @SerrePositivity.KST.SConstruction.monicKPrismRawLevelFamily
#print axioms SerrePositivity.KST.SConstruction.monicKPrismRawLevelFamily

#check @SerrePositivity.KST.SConstruction.monicKPrismRawSequenceCompatibility
#print axioms SerrePositivity.KST.SConstruction.monicKPrismRawSequenceCompatibility

#check @SerrePositivity.KST.SConstruction.monicKPrismRawSequenceCompatibility_h
#print axioms SerrePositivity.KST.SConstruction.monicKPrismRawSequenceCompatibility_h

#check @SerrePositivity.KST.SConstruction.monicKPrismRawSequenceCompatibility_boundary
#print axioms SerrePositivity.KST.SConstruction.monicKPrismRawSequenceCompatibility_boundary

#check @SerrePositivity.KST.SConstruction.exists_fibration_family_transport
#print axioms SerrePositivity.KST.SConstruction.exists_fibration_family_transport

#check @SerrePositivity.KST.SConstruction.exists_familyHomotopyChain_lift_with_trace
#print axioms SerrePositivity.KST.SConstruction.exists_familyHomotopyChain_lift_with_trace

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainLiftData
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainLiftData

#check @SerrePositivity.KST.SConstruction.TracedSequenceFamilyStage
#print axioms SerrePositivity.KST.SConstruction.TracedSequenceFamilyStage

#check @SerrePositivity.KST.SConstruction.tracedSequenceFamilyNext
#print axioms SerrePositivity.KST.SConstruction.tracedSequenceFamilyNext

#check @SerrePositivity.KST.SConstruction.tracedSequenceFamilyStage
#print axioms SerrePositivity.KST.SConstruction.tracedSequenceFamilyStage

#check @SerrePositivity.KST.SConstruction.tracedSequenceFamilyStage_trace
#print axioms SerrePositivity.KST.SConstruction.tracedSequenceFamilyStage_trace

#check @SerrePositivity.KST.SConstruction.tracedSequenceFamilyRectification
#print axioms SerrePositivity.KST.SConstruction.tracedSequenceFamilyRectification

#check @SerrePositivity.KST.SConstruction.tracedSequenceFamilyRectification_evaluation
#print axioms SerrePositivity.KST.SConstruction.tracedSequenceFamilyRectification_evaluation

#check @SerrePositivity.KST.SConstruction.tracedSequenceFamilyRectification_chain
#print axioms SerrePositivity.KST.SConstruction.tracedSequenceFamilyRectification_chain

#check @SerrePositivity.KST.SConstruction.tracedSequenceFamilyRectification_zero
#print axioms SerrePositivity.KST.SConstruction.tracedSequenceFamilyRectification_zero

#check @SerrePositivity.KST.SConstruction.tracedSequenceBoundaryCompatibility
#print axioms SerrePositivity.KST.SConstruction.tracedSequenceBoundaryCompatibility

#check @SerrePositivity.KST.SConstruction.TracedSequenceBoundaryData
#print axioms SerrePositivity.KST.SConstruction.TracedSequenceBoundaryData

#check @SerrePositivity.KST.SConstruction.canonicalTracedSequenceBoundaryData
#print axioms SerrePositivity.KST.SConstruction.canonicalTracedSequenceBoundaryData

#check @SerrePositivity.KST.SConstruction.tracedSequenceBoundaryMap
#print axioms SerrePositivity.KST.SConstruction.tracedSequenceBoundaryMap

#check @SerrePositivity.KST.SConstruction.tracedSequenceBoundaryMap_evaluation
#print axioms SerrePositivity.KST.SConstruction.tracedSequenceBoundaryMap_evaluation

#check @SerrePositivity.KST.SConstruction.PrescribedSequenceFamilyStage
#print axioms SerrePositivity.KST.SConstruction.PrescribedSequenceFamilyStage

#check @SerrePositivity.KST.SConstruction.prescribedSequenceFamilyNext
#print axioms SerrePositivity.KST.SConstruction.prescribedSequenceFamilyNext

#check @SerrePositivity.KST.SConstruction.prescribedSequenceFamilyStage
#print axioms SerrePositivity.KST.SConstruction.prescribedSequenceFamilyStage

#check @SerrePositivity.KST.SConstruction.prescribedSequenceFamilyRectification
#print axioms SerrePositivity.KST.SConstruction.prescribedSequenceFamilyRectification

#check @SerrePositivity.KST.SConstruction.prescribedSequenceFamilyRectification_evaluation
#print axioms SerrePositivity.KST.SConstruction.prescribedSequenceFamilyRectification_evaluation

#check @SerrePositivity.KST.SConstruction.prescribedSequenceFamilyRectification_boundary
#print axioms SerrePositivity.KST.SConstruction.prescribedSequenceFamilyRectification_boundary

#check @SerrePositivity.KST.SConstruction.prescribedSequenceFamilyStage_boundary_trace
#print axioms SerrePositivity.KST.SConstruction.prescribedSequenceFamilyStage_boundary_trace

#check @SerrePositivity.KST.SConstruction.prescribedSequenceFamilyStage_trace
#print axioms SerrePositivity.KST.SConstruction.prescribedSequenceFamilyStage_trace

#check @SerrePositivity.KST.SConstruction.prescribedSequenceFamilyRectification_zero
#print axioms SerrePositivity.KST.SConstruction.prescribedSequenceFamilyRectification_zero

#check @SerrePositivity.KST.SConstruction.kRawFamilyLiftData
#print axioms SerrePositivity.KST.SConstruction.kRawFamilyLiftData

#check @SerrePositivity.KST.SConstruction.kTracedBoundaryLiftData
#print axioms SerrePositivity.KST.SConstruction.kTracedBoundaryLiftData

#check @SerrePositivity.KST.SConstruction.kTracedFamilyLiftData
#print axioms SerrePositivity.KST.SConstruction.kTracedFamilyLiftData

#check @SerrePositivity.KST.SConstruction.kTracedFamilyLiftData_boundary
#print axioms SerrePositivity.KST.SConstruction.kTracedFamilyLiftData_boundary

#check @SerrePositivity.KST.SConstruction.kTracedFamilyLiftData_projection
#print axioms SerrePositivity.KST.SConstruction.kTracedFamilyLiftData_projection

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedBoundary
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedBoundary

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedRawFamily
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedRawFamily

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedBFBoundary
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedBFBoundary

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedBFFamily
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedBFFamily

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedBFFamily_boundary
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedBFFamily_boundary

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedBFFamily_projection
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedBFFamily_projection

#check @SerrePositivity.KST.SConstruction.TracedSequenceFamilyStage.mk
#print axioms SerrePositivity.KST.SConstruction.TracedSequenceFamilyStage.mk

#check @SerrePositivity.KST.SConstruction.TracedSequenceFamilyStage.val
#print axioms SerrePositivity.KST.SConstruction.TracedSequenceFamilyStage.val

#check @SerrePositivity.KST.SConstruction.TracedSequenceFamilyStage.chain
#print axioms SerrePositivity.KST.SConstruction.TracedSequenceFamilyStage.chain

#check @SerrePositivity.KST.SConstruction.TracedSequenceBoundaryData.mk
#print axioms SerrePositivity.KST.SConstruction.TracedSequenceBoundaryData.mk

#check @SerrePositivity.KST.SConstruction.TracedSequenceBoundaryData.stage
#print axioms SerrePositivity.KST.SConstruction.TracedSequenceBoundaryData.stage

#check @SerrePositivity.KST.SConstruction.TracedSequenceBoundaryData.zero
#print axioms SerrePositivity.KST.SConstruction.TracedSequenceBoundaryData.zero

#check @SerrePositivity.KST.SConstruction.TracedSequenceBoundaryData.zero_trace
#print axioms SerrePositivity.KST.SConstruction.TracedSequenceBoundaryData.zero_trace

#check @SerrePositivity.KST.SConstruction.TracedSequenceBoundaryData.comm
#print axioms SerrePositivity.KST.SConstruction.TracedSequenceBoundaryData.comm

#check @SerrePositivity.KST.SConstruction.TracedSequenceBoundaryData.trace
#print axioms SerrePositivity.KST.SConstruction.TracedSequenceBoundaryData.trace

#check @SerrePositivity.KST.SConstruction.PrescribedSequenceFamilyStage.mk
#print axioms SerrePositivity.KST.SConstruction.PrescribedSequenceFamilyStage.mk

#check @SerrePositivity.KST.SConstruction.PrescribedSequenceFamilyStage.val
#print axioms SerrePositivity.KST.SConstruction.PrescribedSequenceFamilyStage.val

#check @SerrePositivity.KST.SConstruction.PrescribedSequenceFamilyStage.chain
#print axioms SerrePositivity.KST.SConstruction.PrescribedSequenceFamilyStage.chain

#check @SerrePositivity.KST.SConstruction.PrescribedSequenceFamilyStage.boundary
#print axioms SerrePositivity.KST.SConstruction.PrescribedSequenceFamilyStage.boundary

#check @SerrePositivity.KST.SConstruction.PrescribedSequenceFamilyStage.boundary_trace
#print axioms SerrePositivity.KST.SConstruction.PrescribedSequenceFamilyStage.boundary_trace


#check @SerrePositivity.KST.SConstruction.monicKPrismTracedBFFamily_evaluation
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedBFFamily_evaluation

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedRawFamily_chain
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedRawFamily_chain

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedRawFamily_zero
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedRawFamily_zero

#check @SerrePositivity.KST.SConstruction.extendedTracedSequenceBoundaryData
#print axioms SerrePositivity.KST.SConstruction.extendedTracedSequenceBoundaryData

#check @SerrePositivity.KST.SConstruction.extendedTracedSequenceBoundaryData_map
#print axioms SerrePositivity.KST.SConstruction.extendedTracedSequenceBoundaryData_map

#check @SerrePositivity.KST.SConstruction.prescribedSequenceFamilyRectification_extension
#print axioms SerrePositivity.KST.SConstruction.prescribedSequenceFamilyRectification_extension

#check @SerrePositivity.KST.SConstruction.prescribedSequenceFamilyStage_extension_trace
#print axioms SerrePositivity.KST.SConstruction.prescribedSequenceFamilyStage_extension_trace

#check @SerrePositivity.KST.SConstruction.kIteratedTracedFamilyLiftData
#print axioms SerrePositivity.KST.SConstruction.kIteratedTracedFamilyLiftData

#check @SerrePositivity.KST.SConstruction.kIteratedTracedFamilyLiftData_intermediate
#print axioms SerrePositivity.KST.SConstruction.kIteratedTracedFamilyLiftData_intermediate

#check @SerrePositivity.KST.SConstruction.kIteratedTracedFamilyLiftData_boundary
#print axioms SerrePositivity.KST.SConstruction.kIteratedTracedFamilyLiftData_boundary

#check @SerrePositivity.KST.SConstruction.kIteratedTracedFamilyLiftData_projection
#print axioms SerrePositivity.KST.SConstruction.kIteratedTracedFamilyLiftData_projection

#check @SerrePositivity.KST.SConstruction.kRawFamilyComparison
#print axioms SerrePositivity.KST.SConstruction.kRawFamilyComparison

#check @SerrePositivity.KST.SConstruction.kRawFamilyComparison_projection
#print axioms SerrePositivity.KST.SConstruction.kRawFamilyComparison_projection

#check @SerrePositivity.KST.SConstruction.kRawFamilyComparison_boundary
#print axioms SerrePositivity.KST.SConstruction.kRawFamilyComparison_boundary

#check @SerrePositivity.KST.SConstruction.kDirectTracedFamilyLiftData
#print axioms SerrePositivity.KST.SConstruction.kDirectTracedFamilyLiftData

#check @SerrePositivity.KST.SConstruction.kIteratedTracedFamilyComparison
#print axioms SerrePositivity.KST.SConstruction.kIteratedTracedFamilyComparison

#check @SerrePositivity.KST.SConstruction.kIteratedTracedFamilyComparison_projection
#print axioms SerrePositivity.KST.SConstruction.kIteratedTracedFamilyComparison_projection

#check @SerrePositivity.KST.SConstruction.kIteratedTracedFamilyComparison_boundary
#print axioms SerrePositivity.KST.SConstruction.kIteratedTracedFamilyComparison_boundary

#check @SerrePositivity.KST.SConstruction.kPrescribedRawFamilyComparisonData
#print axioms SerrePositivity.KST.SConstruction.kPrescribedRawFamilyComparisonData

#check @SerrePositivity.KST.SConstruction.kPrescribedRawFamilyComparisonData_projection
#print axioms SerrePositivity.KST.SConstruction.kPrescribedRawFamilyComparisonData_projection

#check @SerrePositivity.KST.SConstruction.kPrescribedRawFamilyComparisonData_boundary
#print axioms SerrePositivity.KST.SConstruction.kPrescribedRawFamilyComparisonData_boundary

#check @SerrePositivity.KST.SConstruction.familyHomotopyChain_eq_of_trace_nil
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChain_eq_of_trace_nil

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainTargetTransport
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainTargetTransport

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainTargetTransport_trace
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainTargetTransport_trace

#check @SerrePositivity.KST.SConstruction.familyHomotopyPairLeft
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyPairLeft

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainPairLeft
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainPairLeft

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainPairLeft_trace
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainPairLeft_trace

#check @SerrePositivity.KST.SConstruction.pointedConstantCompositionSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.pointedConstantCompositionSimplicialCategory

#check @SerrePositivity.KST.SConstruction.pointedFamilyConstant_eq
#print axioms SerrePositivity.KST.SConstruction.pointedFamilyConstant_eq

#check @SerrePositivity.KST.SConstruction.pointedFamilyComposition_const_right
#print axioms SerrePositivity.KST.SConstruction.pointedFamilyComposition_const_right

#check @SerrePositivity.KST.SConstruction.pointedFamilyComposition_const_left
#print axioms SerrePositivity.KST.SConstruction.pointedFamilyComposition_const_left

#check @SerrePositivity.KST.SConstruction.compositeCorrectionSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.compositeCorrectionSimplicialCategory

#check @SerrePositivity.KST.SConstruction.pointedCompositeCorrectionChain
#print axioms SerrePositivity.KST.SConstruction.pointedCompositeCorrectionChain

#check @SerrePositivity.KST.SConstruction.pointedCompositeCorrectionChain_trace
#print axioms SerrePositivity.KST.SConstruction.pointedCompositeCorrectionChain_trace

#check @SerrePositivity.KST.SConstruction.prismCompositionSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.prismCompositionSimplicialCategory

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedStage
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedStage

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedRawFamily_evaluation
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedRawFamily_evaluation

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedCompositionFamily
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedCompositionFamily

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedRawComposition
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedRawComposition

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedCompositionFamily_projection
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedCompositionFamily_projection

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedRawComposition_evaluation
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedRawComposition_evaluation

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedCompositeCorrectionChain
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedCompositeCorrectionChain

#check @SerrePositivity.KST.SConstruction.prismCompositionTraceSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.prismCompositionTraceSimplicialCategory

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeFirstTrace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeFirstTrace

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondTrace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondTrace

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedCompositeCorrectionChain_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedCompositeCorrectionChain_trace

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedCompositionFamily_boundary
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedCompositionFamily_boundary

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedCompositeCorrectionChain_zero_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedCompositeCorrectionChain_zero_trace

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedRawComposition_zero
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedRawComposition_zero

#check @SerrePositivity.KST.SConstruction.familyInterchangeSquare
#print axioms SerrePositivity.KST.SConstruction.familyInterchangeSquare

#check @SerrePositivity.KST.SConstruction.familyInterchangeSquare_second_zero
#print axioms SerrePositivity.KST.SConstruction.familyInterchangeSquare_second_zero

#check @SerrePositivity.KST.SConstruction.familyInterchangeSquare_second_one
#print axioms SerrePositivity.KST.SConstruction.familyInterchangeSquare_second_one

#check @SerrePositivity.KST.SConstruction.familyInterchangeSquare_first_zero
#print axioms SerrePositivity.KST.SConstruction.familyInterchangeSquare_first_zero

#check @SerrePositivity.KST.SConstruction.familyInterchangeSquare_first_one
#print axioms SerrePositivity.KST.SConstruction.familyInterchangeSquare_first_one

#check @SerrePositivity.KST.SConstruction.familyInterchangeSquare_restrict
#print axioms SerrePositivity.KST.SConstruction.familyInterchangeSquare_restrict

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainInterchangeSquares
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainInterchangeSquares

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainInterchangeSquares_second_zero
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainInterchangeSquares_second_zero

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainInterchangeSquares_second_one
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainInterchangeSquares_second_one

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainInterchangeSquares_first_zero
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainInterchangeSquares_first_zero

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainInterchangeSquares_first_one
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainInterchangeSquares_first_one

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainInterchangeSquares_restrict
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainInterchangeSquares_restrict

#check @SerrePositivity.KST.SConstruction.familyHomotopyChainInterchangeSquares_glue
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainInterchangeSquares_glue

#check @SerrePositivity.KST.SConstruction.pointedCompatibilityInterchangeSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.pointedCompatibilityInterchangeSimplicialCategory

#check @SerrePositivity.KST.SConstruction.pointedCompatibilityInterchangeSquares
#print axioms SerrePositivity.KST.SConstruction.pointedCompatibilityInterchangeSquares

#check @SerrePositivity.KST.SConstruction.pointedCompatibilityInterchangeSquares_second_zero
#print axioms SerrePositivity.KST.SConstruction.pointedCompatibilityInterchangeSquares_second_zero

#check @SerrePositivity.KST.SConstruction.pointedCompatibilityInterchangeSquares_second_one
#print axioms SerrePositivity.KST.SConstruction.pointedCompatibilityInterchangeSquares_second_one

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeCompatibility
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeCompatibility

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeCompatibility_h
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeCompatibility_h

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeCompatibility_boundary
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeCompatibility_boundary

#check @SerrePositivity.KST.SConstruction.monicKPrismCompatibilityInterchangeSquares
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompatibilityInterchangeSquares

#check @SerrePositivity.KST.SConstruction.monicKPrismCompatibilityInterchangeTrace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompatibilityInterchangeTrace

#check @SerrePositivity.KST.SConstruction.monicKPrismCompatibilityInterchangeSquares_second_zero
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompatibilityInterchangeSquares_second_zero

#check @SerrePositivity.KST.SConstruction.monicKPrismCompatibilityInterchangeSquares_second_one
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompatibilityInterchangeSquares_second_one

#check @SerrePositivity.KST.SConstruction.projectedCompositionTraceSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.projectedCompositionTraceSimplicialCategory

#check @SerrePositivity.KST.SConstruction.pointedMapping_post_pre
#print axioms SerrePositivity.KST.SConstruction.pointedMapping_post_pre

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedStage_projection_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedStage_projection_trace

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeFirstTrace_projection
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeFirstTrace_projection

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeFirstTrace_projection_squares
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeFirstTrace_projection_squares

#check @SerrePositivity.KST.SConstruction.monicKPrismCompatibilityInterchangeSquares_glue
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompatibilityInterchangeSquares_glue

#check @SerrePositivity.KST.SConstruction.enriched_left_compatible_comp
#print axioms SerrePositivity.KST.SConstruction.enriched_left_compatible_comp

#check @SerrePositivity.KST.SConstruction.enriched_functor_comp_post
#print axioms SerrePositivity.KST.SConstruction.enriched_functor_comp_post

#check @SerrePositivity.KST.SConstruction.compatibleFamilyCompositionPointedCategory
#print axioms SerrePositivity.KST.SConstruction.compatibleFamilyCompositionPointedCategory

#check @SerrePositivity.KST.SConstruction.familyDiagonal_tensorHom
#print axioms SerrePositivity.KST.SConstruction.familyDiagonal_tensorHom

#check @SerrePositivity.KST.SConstruction.pointed_left_compatible_lift
#print axioms SerrePositivity.KST.SConstruction.pointed_left_compatible_lift

#check @SerrePositivity.KST.SConstruction.pointed_suspension_comp_lift
#print axioms SerrePositivity.KST.SConstruction.pointed_suspension_comp_lift

#check @SerrePositivity.KST.SConstruction.spectrumCylinderCompositionPointedCategory
#print axioms SerrePositivity.KST.SConstruction.spectrumCylinderCompositionPointedCategory

#check @SerrePositivity.KST.SConstruction.spectrumCylinderComposite
#print axioms SerrePositivity.KST.SConstruction.spectrumCylinderComposite

#check @SerrePositivity.KST.SConstruction.spectrumSuspendedCylinderComposite
#print axioms SerrePositivity.KST.SConstruction.spectrumSuspendedCylinderComposite

#check @SerrePositivity.KST.SConstruction.spectrumCylinderComposite_projection
#print axioms SerrePositivity.KST.SConstruction.spectrumCylinderComposite_projection

#check @SerrePositivity.KST.SConstruction.spectrumSuspendedCylinderComposite_step
#print axioms SerrePositivity.KST.SConstruction.spectrumSuspendedCylinderComposite_step

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondTrace_cylinders
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondTrace_cylinders

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondCompatibility
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondCompatibility

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondTrace_projection
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondTrace_projection

#check @SerrePositivity.KST.SConstruction.suspendedMiddleTransferPointedCategory
#print axioms SerrePositivity.KST.SConstruction.suspendedMiddleTransferPointedCategory

#check @SerrePositivity.KST.SConstruction.pointed_middle_comp_lift
#print axioms SerrePositivity.KST.SConstruction.pointed_middle_comp_lift

#check @SerrePositivity.KST.SConstruction.pointed_suspension_middle_lift
#print axioms SerrePositivity.KST.SConstruction.pointed_suspension_middle_lift

#check @SerrePositivity.KST.SConstruction.familyInterchangeCylinderHomotopy
#print axioms SerrePositivity.KST.SConstruction.familyInterchangeCylinderHomotopy

#check @SerrePositivity.KST.SConstruction.familyInterchangeCylinderChain
#print axioms SerrePositivity.KST.SConstruction.familyInterchangeCylinderChain

#check @SerrePositivity.KST.SConstruction.familyInterchangeCylinderChain_trace
#print axioms SerrePositivity.KST.SConstruction.familyInterchangeCylinderChain_trace

#check @SerrePositivity.KST.SConstruction.compositeCylinderTransportPointedCategory
#print axioms SerrePositivity.KST.SConstruction.compositeCylinderTransportPointedCategory

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeCompatibilityAt
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeCompatibilityAt

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeCompatibilityTransportChain
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeCompatibilityTransportChain

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondCompatibility_at_stage
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondCompatibility_at_stage

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondCompatibilityTransport
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondCompatibilityTransport

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondCompatibilityTransport_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondCompatibilityTransport_trace

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeFirstCompatibility
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeFirstCompatibility

#check @SerrePositivity.KST.SConstruction.monicKPrismTracedCompositeCorrectionChain_projection_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedCompositeCorrectionChain_projection_trace

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondCompatibilityTransport_zero_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondCompatibilityTransport_zero_trace

#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondCompatibility_zero
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondCompatibility_zero

#check @SerrePositivity.KST.SConstruction.trianglePrismHorizontal
#print axioms SerrePositivity.KST.SConstruction.trianglePrismHorizontal

#check @SerrePositivity.KST.SConstruction.trianglePrismTime
#print axioms SerrePositivity.KST.SConstruction.trianglePrismTime

#check @SerrePositivity.KST.SConstruction.trianglePrismTetrahedron
#print axioms SerrePositivity.KST.SConstruction.trianglePrismTetrahedron

#check @SerrePositivity.KST.SConstruction.trianglePrismEdge
#print axioms SerrePositivity.KST.SConstruction.trianglePrismEdge

#check @SerrePositivity.KST.SConstruction.trianglePrismUpper
#print axioms SerrePositivity.KST.SConstruction.trianglePrismUpper

#check @SerrePositivity.KST.SConstruction.trianglePrismLower
#print axioms SerrePositivity.KST.SConstruction.trianglePrismLower

#check @SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_shared_first
#print axioms SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_shared_first

#check @SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_shared_second
#print axioms SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_shared_second

#check @SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_composite_upper
#print axioms SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_composite_upper

#check @SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_composite_lower
#print axioms SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_composite_lower

#check @SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_first_upper
#print axioms SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_first_upper

#check @SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_first_lower
#print axioms SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_first_lower

#check @SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_second_upper
#print axioms SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_second_upper

#check @SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_second_lower
#print axioms SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_second_lower

#check @SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_top
#print axioms SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_top

#check @SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_bottom
#print axioms SerrePositivity.KST.SConstruction.trianglePrismTetrahedron_bottom

#check @SerrePositivity.KST.SConstruction.trianglePrismImage
#print axioms SerrePositivity.KST.SConstruction.trianglePrismImage

#check @SerrePositivity.KST.SConstruction.trianglePrismSource
#print axioms SerrePositivity.KST.SConstruction.trianglePrismSource

#check @SerrePositivity.KST.SConstruction.trianglePrismTarget
#print axioms SerrePositivity.KST.SConstruction.trianglePrismTarget

#check @SerrePositivity.KST.SConstruction.trianglePrismImage_source
#print axioms SerrePositivity.KST.SConstruction.trianglePrismImage_source

#check @SerrePositivity.KST.SConstruction.trianglePrismImage_target
#print axioms SerrePositivity.KST.SConstruction.trianglePrismImage_target

#check @SerrePositivity.KST.SConstruction.trianglePrismImage_hom
#print axioms SerrePositivity.KST.SConstruction.trianglePrismImage_hom

#check @SerrePositivity.KST.SConstruction.trianglePrismImage_face
#print axioms SerrePositivity.KST.SConstruction.trianglePrismImage_face

#check @SerrePositivity.KST.SConstruction.trianglePrismImage_shared_first
#print axioms SerrePositivity.KST.SConstruction.trianglePrismImage_shared_first

#check @SerrePositivity.KST.SConstruction.trianglePrismImage_shared_second
#print axioms SerrePositivity.KST.SConstruction.trianglePrismImage_shared_second

#check @SerrePositivity.KST.SConstruction.trianglePrismMappingSquare
#print axioms SerrePositivity.KST.SConstruction.trianglePrismMappingSquare

#check @SerrePositivity.KST.SConstruction.trianglePrismMappingSquare_skip_first
#print axioms SerrePositivity.KST.SConstruction.trianglePrismMappingSquare_skip_first

#check @SerrePositivity.KST.SConstruction.trianglePrismMappingSquare_skip_second
#print axioms SerrePositivity.KST.SConstruction.trianglePrismMappingSquare_skip_second

#check @SerrePositivity.KST.SConstruction.trianglePrismMappingSquare_include_first
#print axioms SerrePositivity.KST.SConstruction.trianglePrismMappingSquare_include_first

#check @SerrePositivity.KST.SConstruction.trianglePrismMappingSquare_include_second
#print axioms SerrePositivity.KST.SConstruction.trianglePrismMappingSquare_include_second

#check @SerrePositivity.KST.SConstruction.trianglePrismMappingSquare_shared_first
#print axioms SerrePositivity.KST.SConstruction.trianglePrismMappingSquare_shared_first

#check @SerrePositivity.KST.SConstruction.trianglePrismMappingSquare_shared_second
#print axioms SerrePositivity.KST.SConstruction.trianglePrismMappingSquare_shared_second

#check @SerrePositivity.KST.SConstruction.kCompositionPrismFacesPointedCategory
#print axioms SerrePositivity.KST.SConstruction.kCompositionPrismFacesPointedCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionPrism
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionPrism

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionPrism_first
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionPrism_first

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionPrism_second
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionPrism_second

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionPrism_composite
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionPrism_composite

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_composite_upper
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_composite_upper

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_composite_lower
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_composite_lower

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_first_upper
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_first_upper

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_first_lower
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_first_lower

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_second_upper
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_second_upper

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_second_lower
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_second_lower

#check @SerrePositivity.KST.SConstruction.triangleFlaggedPath_zero
#print axioms SerrePositivity.KST.SConstruction.triangleFlaggedPath_zero

#check @SerrePositivity.KST.SConstruction.triangleFlaggedPath_one
#print axioms SerrePositivity.KST.SConstruction.triangleFlaggedPath_one

#check @SerrePositivity.KST.SConstruction.trianglePathInterval_original_edge
#print axioms SerrePositivity.KST.SConstruction.trianglePathInterval_original_edge

#check @SerrePositivity.KST.SConstruction.coherentTriangleTrace_composition_edge
#print axioms SerrePositivity.KST.SConstruction.coherentTriangleTrace_composition_edge

#check @SerrePositivity.KST.SConstruction.coherentTriangleTrace_specified_edge_heq
#print axioms SerrePositivity.KST.SConstruction.coherentTriangleTrace_specified_edge_heq

#check @SerrePositivity.KST.SConstruction.simplicialHom_post_eqToHom_heq
#print axioms SerrePositivity.KST.SConstruction.simplicialHom_post_eqToHom_heq

#check @SerrePositivity.KST.SConstruction.coherentTriangleTrace_specified_edge
#print axioms SerrePositivity.KST.SConstruction.coherentTriangleTrace_specified_edge

#check @SerrePositivity.KST.SConstruction.coherentTriangleTrace_specified_face
#print axioms SerrePositivity.KST.SConstruction.coherentTriangleTrace_specified_face

#check @SerrePositivity.KST.SConstruction.kCompositionPrismSquaresPointedCategory
#print axioms SerrePositivity.KST.SConstruction.kCompositionPrismSquaresPointedCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalPrism_bottom_object
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalPrism_bottom_object

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionPrism_source
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionPrism_source

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionPrism_target
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionPrism_target

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionPrism_hom
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionPrism_hom

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_shared_first
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_shared_first

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_shared_second
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_shared_second

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_composite_upper
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_composite_upper

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_composite_lower
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_composite_lower

#check @SerrePositivity.KST.SConstruction.tetrahedronInitialPath_endpoint
#print axioms SerrePositivity.KST.SConstruction.tetrahedronInitialPath_endpoint

#check @SerrePositivity.KST.SConstruction.tetrahedronFinalPath_endpoint
#print axioms SerrePositivity.KST.SConstruction.tetrahedronFinalPath_endpoint

#check @SerrePositivity.KST.SConstruction.tetrahedronInitialTrace_arrow
#print axioms SerrePositivity.KST.SConstruction.tetrahedronInitialTrace_arrow

#check @SerrePositivity.KST.SConstruction.tetrahedronFinalTrace_arrow
#print axioms SerrePositivity.KST.SConstruction.tetrahedronFinalTrace_arrow

#check @SerrePositivity.KST.SConstruction.enrichedFamilyConstant_eq
#print axioms SerrePositivity.KST.SConstruction.enrichedFamilyConstant_eq

#check @SerrePositivity.KST.SConstruction.enrichedFamilyComposition_const_left
#print axioms SerrePositivity.KST.SConstruction.enrichedFamilyComposition_const_left

#check @SerrePositivity.KST.SConstruction.enrichedFamilyComposition_const_right
#print axioms SerrePositivity.KST.SConstruction.enrichedFamilyComposition_const_right

#check @SerrePositivity.KST.SConstruction.tetrahedronTrace_include_first_whisker
#print axioms SerrePositivity.KST.SConstruction.tetrahedronTrace_include_first_whisker

#check @SerrePositivity.KST.SConstruction.tetrahedronTrace_include_second_whisker
#print axioms SerrePositivity.KST.SConstruction.tetrahedronTrace_include_second_whisker

#check @SerrePositivity.KST.SConstruction.tetrahedronFirstEdgeMap
#print axioms SerrePositivity.KST.SConstruction.tetrahedronFirstEdgeMap

#check @SerrePositivity.KST.SConstruction.tetrahedronLastEdgeMap
#print axioms SerrePositivity.KST.SConstruction.tetrahedronLastEdgeMap

#check @SerrePositivity.KST.SConstruction.tetrahedronFirstEdge_of_face
#print axioms SerrePositivity.KST.SConstruction.tetrahedronFirstEdge_of_face

#check @SerrePositivity.KST.SConstruction.tetrahedronLastEdge_of_face
#print axioms SerrePositivity.KST.SConstruction.tetrahedronLastEdge_of_face

#check @SerrePositivity.KST.SConstruction.tetrahedronTrace_include_first_specified
#print axioms SerrePositivity.KST.SConstruction.tetrahedronTrace_include_first_specified

#check @SerrePositivity.KST.SConstruction.tetrahedronTrace_include_second_specified
#print axioms SerrePositivity.KST.SConstruction.tetrahedronTrace_include_second_specified

#check @SerrePositivity.KST.SConstruction.kCompositionPrismWhiskerFacesPointedCategory
#print axioms SerrePositivity.KST.SConstruction.kCompositionPrismWhiskerFacesPointedCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_first_middle
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_first_middle

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_last_middle
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_last_middle

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_first_last
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_first_last

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_last_first
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_last_first

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_first_upper_post
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_first_upper_post

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_first_lower_post
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_first_lower_post

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_second_upper_pre
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_second_upper_pre

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_second_lower_pre
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_second_lower_pre

#check @SerrePositivity.KST.SConstruction.coherentTriangleTrace_strict
#print axioms SerrePositivity.KST.SConstruction.coherentTriangleTrace_strict

#check @SerrePositivity.KST.SConstruction.kCompositionPrismStrictFacesPointedCategory
#print axioms SerrePositivity.KST.SConstruction.kCompositionPrismStrictFacesPointedCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_top_strict
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_top_strict

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_bottom_strict
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_bottom_strict

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_top_trace_constant
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_top_trace_constant

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_bottom_trace_constant
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionImage_bottom_trace_constant

#check @SerrePositivity.KST.SConstruction.kCompositionPrismExteriorConstantsPointedCategory
#print axioms SerrePositivity.KST.SConstruction.kCompositionPrismExteriorConstantsPointedCategory

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_exterior_upper_constant
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_exterior_upper_constant

#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_exterior_lower_constant
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionMappingSquare_exterior_lower_constant

-- 三正方形と指定外側三角形の同時貼り合わせ。
#check @SerrePositivity.KST.SConstruction.pastingSquareVertical
#print axioms SerrePositivity.KST.SConstruction.pastingSquareVertical
#check @SerrePositivity.KST.SConstruction.pastingSquareHorizontal
#print axioms SerrePositivity.KST.SConstruction.pastingSquareHorizontal
#check @SerrePositivity.KST.SConstruction.pastingIntervalVertex
#print axioms SerrePositivity.KST.SConstruction.pastingIntervalVertex
#check @SerrePositivity.KST.SConstruction.pastingSquareHorizontal_start
#print axioms SerrePositivity.KST.SConstruction.pastingSquareHorizontal_start
#check @SerrePositivity.KST.SConstruction.pastingSquareVertical_start
#print axioms SerrePositivity.KST.SConstruction.pastingSquareVertical_start
#check @SerrePositivity.KST.SConstruction.firstTwoSquarePasting
#print axioms SerrePositivity.KST.SConstruction.firstTwoSquarePasting
#check @SerrePositivity.KST.SConstruction.firstTwoSquareInclusion
#print axioms SerrePositivity.KST.SConstruction.firstTwoSquareInclusion
#check @SerrePositivity.KST.SConstruction.threeSquareAttachingEdge
#print axioms SerrePositivity.KST.SConstruction.threeSquareAttachingEdge
#check @SerrePositivity.KST.SConstruction.threeSquarePasting
#print axioms SerrePositivity.KST.SConstruction.threeSquarePasting
#check @SerrePositivity.KST.SConstruction.threeSquareInclusion
#print axioms SerrePositivity.KST.SConstruction.threeSquareInclusion
#check @SerrePositivity.KST.SConstruction.threeSquareInclusion_shared_first
#print axioms SerrePositivity.KST.SConstruction.threeSquareInclusion_shared_first
#check @SerrePositivity.KST.SConstruction.threeSquareInclusion_shared_second
#print axioms SerrePositivity.KST.SConstruction.threeSquareInclusion_shared_second
#check @SerrePositivity.KST.SConstruction.threeSquarePastingMap
#print axioms SerrePositivity.KST.SConstruction.threeSquarePastingMap
#check @SerrePositivity.KST.SConstruction.threeSquarePastingMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.threeSquarePastingMap_inclusion
#check @SerrePositivity.KST.SConstruction.threeSquareSpanLeft
#print axioms SerrePositivity.KST.SConstruction.threeSquareSpanLeft
#check @SerrePositivity.KST.SConstruction.threeSquareSpanRight
#print axioms SerrePositivity.KST.SConstruction.threeSquareSpanRight
#check @SerrePositivity.KST.SConstruction.threeSquareSpan_start
#print axioms SerrePositivity.KST.SConstruction.threeSquareSpan_start
#check @SerrePositivity.KST.SConstruction.threeSquareSpanHorn
#print axioms SerrePositivity.KST.SConstruction.threeSquareSpanHorn
#check @SerrePositivity.KST.SConstruction.threeSquareSpanHorn_left
#print axioms SerrePositivity.KST.SConstruction.threeSquareSpanHorn_left
#check @SerrePositivity.KST.SConstruction.threeSquareSpanHorn_right
#print axioms SerrePositivity.KST.SConstruction.threeSquareSpanHorn_right
#check @SerrePositivity.KST.SConstruction.threeSquareAllHorns
#print axioms SerrePositivity.KST.SConstruction.threeSquareAllHorns
#check @SerrePositivity.KST.SConstruction.threeSquareAllHornInclusions
#print axioms SerrePositivity.KST.SConstruction.threeSquareAllHornInclusions
#check @SerrePositivity.KST.SConstruction.threeSquareTrianglePasting
#print axioms SerrePositivity.KST.SConstruction.threeSquareTrianglePasting
#check @SerrePositivity.KST.SConstruction.threeSquareTriangleSquare
#print axioms SerrePositivity.KST.SConstruction.threeSquareTriangleSquare
#check @SerrePositivity.KST.SConstruction.threeSquareTriangleCell
#print axioms SerrePositivity.KST.SConstruction.threeSquareTriangleCell
#check @SerrePositivity.KST.SConstruction.threeSquareTrianglePasting_compatible
#print axioms SerrePositivity.KST.SConstruction.threeSquareTrianglePasting_compatible
#check @SerrePositivity.KST.SConstruction.threeSquareTrianglePastingMap
#print axioms SerrePositivity.KST.SConstruction.threeSquareTrianglePastingMap
#check @SerrePositivity.KST.SConstruction.threeSquareTrianglePastingMap_square
#print axioms SerrePositivity.KST.SConstruction.threeSquareTrianglePastingMap_square
#check @SerrePositivity.KST.SConstruction.threeSquareTrianglePastingMap_triangle
#print axioms SerrePositivity.KST.SConstruction.threeSquareTrianglePastingMap_triangle
#check @SerrePositivity.KST.SConstruction.kCompositionPastingSquaresPointedCategory
#print axioms SerrePositivity.KST.SConstruction.kCompositionPastingSquaresPointedCategory
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionPastingSquares
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionPastingSquares
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionPastingSquares_square
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionPastingSquares_square
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionPastingSquares_exterior_upper_constant
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionPastingSquares_exterior_upper_constant
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionPastingSquares_exterior_lower_constant
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionPastingSquares_exterior_lower_constant
#check @SerrePositivity.KST.SConstruction.kCompositionPastingTrianglesPointedCategory
#print axioms SerrePositivity.KST.SConstruction.kCompositionPastingTrianglesPointedCategory
#check @SerrePositivity.KST.SConstruction.kKanOriginalOuterTriangle
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalOuterTriangle
#check @SerrePositivity.KST.SConstruction.kKanOriginalOuterTriangle_upper
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalOuterTriangle_upper
#check @SerrePositivity.KST.SConstruction.kKanOriginalOuterTriangle_lower
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalOuterTriangle_lower
#check @SerrePositivity.KST.SConstruction.kKanOriginalOuterTriangle_compatibility
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalOuterTriangle_compatibility
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionPastingTriangle
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionPastingTriangle
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionPastingTriangle_upper
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionPastingTriangle_upper
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionPastingTriangle_lower
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionPastingTriangle_lower
#check @SerrePositivity.KST.SConstruction.kCompositionSpecifiedPastingPointedCategory
#print axioms SerrePositivity.KST.SConstruction.kCompositionSpecifiedPastingPointedCategory
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionSpecifiedPasting
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionSpecifiedPasting
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionSpecifiedPasting_square
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionSpecifiedPasting_square
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionSpecifiedPasting_triangle
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionSpecifiedPasting_triangle
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionSpecifiedPasting_composite_compatibility
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionSpecifiedPasting_composite_compatibility
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionSpecifiedPasting_first_compatibility
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionSpecifiedPasting_first_compatibility
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionSpecifiedPasting_second_compatibility
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionSpecifiedPasting_second_compatibility
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionSpecifiedPasting_exterior_upper_constant
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionSpecifiedPasting_exterior_upper_constant
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionSpecifiedPasting_exterior_lower_constant
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionSpecifiedPasting_exterior_lower_constant

-- 元の六セルからの端点固定の実比較三角形。
#check @SerrePositivity.KST.SConstruction.MappingSquareBoundaryData
#print axioms SerrePositivity.KST.SConstruction.MappingSquareBoundaryData
#check @SerrePositivity.KST.SConstruction.MappingSquareBoundaryData.homMk_comp
#print axioms SerrePositivity.KST.SConstruction.MappingSquareBoundaryData.homMk_comp
#check @SerrePositivity.KST.SConstruction.MappingSquareBoundaryData.mk
#print axioms SerrePositivity.KST.SConstruction.MappingSquareBoundaryData.mk
#check @SerrePositivity.KST.SConstruction.MappingSquareBoundaryData.square
#print axioms SerrePositivity.KST.SConstruction.MappingSquareBoundaryData.square
#check @SerrePositivity.KST.SConstruction.MappingSquareBoundaryData.bottom_eq
#print axioms SerrePositivity.KST.SConstruction.MappingSquareBoundaryData.bottom_eq
#check @SerrePositivity.KST.SConstruction.MappingSquareBoundaryData.top_eq
#print axioms SerrePositivity.KST.SConstruction.MappingSquareBoundaryData.top_eq
#check @SerrePositivity.KST.SConstruction.MappingSquareBoundaryData.left_eq
#print axioms SerrePositivity.KST.SConstruction.MappingSquareBoundaryData.left_eq
#check @SerrePositivity.KST.SConstruction.MappingSquareBoundaryData.right_eq
#print axioms SerrePositivity.KST.SConstruction.MappingSquareBoundaryData.right_eq
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.whiskered_relation
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.whiskered_relation
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.comparison
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.comparison
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.mk
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.mk
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.origin
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.origin
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.left
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.left
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.bottom
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.bottom
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.upper
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.upper
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.middle
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.middle
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.lower
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.lower
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.upperLeg
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.upperLeg
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.lowerLeg
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.lowerLeg
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.leftLeg
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.leftLeg
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.bottomLeg
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.bottomLeg
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.firstUpper
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.firstUpper
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.firstLower
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.firstLower
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.secondUpper
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.secondUpper
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.secondLower
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.secondLower
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.composite
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.composite
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.first
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.first
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.second
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.second
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.firstSquare
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.firstSquare
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.middleSquare
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.middleSquare
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.lastSquare
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.lastSquare
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.compositeTriangle
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.compositeTriangle
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.firstTriangle
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.firstTriangle
#check @SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.secondTriangle
#print axioms SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData.secondTriangle
#check @SerrePositivity.KST.SConstruction.mappingEdgeRetarget
#print axioms SerrePositivity.KST.SConstruction.mappingEdgeRetarget
#check @SerrePositivity.KST.SConstruction.mappingSquareHorizontalEdge
#print axioms SerrePositivity.KST.SConstruction.mappingSquareHorizontalEdge
#check @SerrePositivity.KST.SConstruction.mappingSquareVerticalEdge
#print axioms SerrePositivity.KST.SConstruction.mappingSquareVerticalEdge
#check @SerrePositivity.KST.SConstruction.mappingSquareHorizontalEdge_map
#print axioms SerrePositivity.KST.SConstruction.mappingSquareHorizontalEdge_map
#check @SerrePositivity.KST.SConstruction.mappingSquareVerticalEdge_map
#print axioms SerrePositivity.KST.SConstruction.mappingSquareVerticalEdge_map
#check @SerrePositivity.KST.SConstruction.mappingOuterTriangleEdge
#print axioms SerrePositivity.KST.SConstruction.mappingOuterTriangleEdge
#check @SerrePositivity.KST.SConstruction.mappingOuterTriangle
#print axioms SerrePositivity.KST.SConstruction.mappingOuterTriangle
#check @SerrePositivity.KST.SConstruction.mappingSquareVertical_shared_corner
#print axioms SerrePositivity.KST.SConstruction.mappingSquareVertical_shared_corner
#check @SerrePositivity.KST.SConstruction.mappingSquareHorizontal_shared_corner
#print axioms SerrePositivity.KST.SConstruction.mappingSquareHorizontal_shared_corner
#check @SerrePositivity.KST.SConstruction.mappingSquareVertical_constant_corner
#print axioms SerrePositivity.KST.SConstruction.mappingSquareVertical_constant_corner
#check @SerrePositivity.KST.SConstruction.mappingSquareHorizontal_constant_corner
#print axioms SerrePositivity.KST.SConstruction.mappingSquareHorizontal_constant_corner
#check @SerrePositivity.KST.SConstruction.mappingIdentityEdge_map
#print axioms SerrePositivity.KST.SConstruction.mappingIdentityEdge_map
#check @SerrePositivity.KST.SConstruction.mappingTriangleFaceEdge
#print axioms SerrePositivity.KST.SConstruction.mappingTriangleFaceEdge
#check @SerrePositivity.KST.SConstruction.threeSquareCompatibilityDataOfMaps
#print axioms SerrePositivity.KST.SConstruction.threeSquareCompatibilityDataOfMaps
#check @SerrePositivity.KST.SConstruction.kCompositionCompatibilityDataPointedCategory
#print axioms SerrePositivity.KST.SConstruction.kCompositionCompatibilityDataPointedCategory
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityData
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityData
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityData_squares
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityData_squares
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityData_triangles
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityData_triangles
#check @SerrePositivity.KST.SConstruction.kCompositionCompatibilityTrianglePointedCategory
#print axioms SerrePositivity.KST.SConstruction.kCompositionCompatibilityTrianglePointedCategory
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityTriangle
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityTriangle
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityData_composite
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityData_composite
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityData_first
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityData_first
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityData_second
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityData_second
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityTriangle_face_first
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityTriangle_face_first
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityTriangle_face_second
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityTriangle_face_second
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityTriangle_face_composite
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityTriangle_face_composite
#check @SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityTriangle_original_faces
#print axioms SerrePositivity.KST.SConstruction.kKanOriginalCompositionCompatibilityTriangle_original_faces
#check @SerrePositivity.KST.SConstruction.monicKPrismOriginalCompositionTrianglePointedCategory
#print axioms SerrePositivity.KST.SConstruction.monicKPrismOriginalCompositionTrianglePointedCategory
#check @SerrePositivity.KST.SConstruction.monicKPrismOriginalCompositionTriangle
#print axioms SerrePositivity.KST.SConstruction.monicKPrismOriginalCompositionTriangle
#check @SerrePositivity.KST.SConstruction.monicKPrismOriginalCompositionTriangle_first
#print axioms SerrePositivity.KST.SConstruction.monicKPrismOriginalCompositionTriangle_first
#check @SerrePositivity.KST.SConstruction.monicKPrismOriginalCompositionTriangle_second
#print axioms SerrePositivity.KST.SConstruction.monicKPrismOriginalCompositionTriangle_second
#check @SerrePositivity.KST.SConstruction.monicKPrismOriginalCompositionTriangle_composite
#print axioms SerrePositivity.KST.SConstruction.monicKPrismOriginalCompositionTriangle_composite

-- 全三辺・指定比較二単体を保つ全精密化の合成適合族。
#check @SerrePositivity.KST.SConstruction.triangleBoundaryFaces
#print axioms SerrePositivity.KST.SConstruction.triangleBoundaryFaces
#check @SerrePositivity.KST.SConstruction.triangleBoundaryFaces_compatible
#print axioms SerrePositivity.KST.SConstruction.triangleBoundaryFaces_compatible
#check @SerrePositivity.KST.SConstruction.triangleBoundaryMap
#print axioms SerrePositivity.KST.SConstruction.triangleBoundaryMap
#check @SerrePositivity.KST.SConstruction.triangleBoundaryMap_face
#print axioms SerrePositivity.KST.SConstruction.triangleBoundaryMap_face
#check @SerrePositivity.KST.SConstruction.trivialKanTriangleLift
#print axioms SerrePositivity.KST.SConstruction.trivialKanTriangleLift
#check @SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleFamilyData
#print axioms SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleFamilyData
#check @SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleFamily
#print axioms SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleFamily
#check @SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleFamily_boundary
#print axioms SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleFamily_boundary
#check @SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleFamily_first
#print axioms SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleFamily_first
#check @SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleFamily_second
#print axioms SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleFamily_second
#check @SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleFamily_composite
#print axioms SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleFamily_composite
#check @SerrePositivity.KST.SConstruction.CompositionStringParameters
#print axioms SerrePositivity.KST.SConstruction.CompositionStringParameters
#check @SerrePositivity.KST.SConstruction.compositionStringDirect
#print axioms SerrePositivity.KST.SConstruction.compositionStringDirect
#check @SerrePositivity.KST.SConstruction.compositionStringDirect_isInitial
#print axioms SerrePositivity.KST.SConstruction.compositionStringDirect_isInitial
#check @SerrePositivity.KST.SConstruction.compositionStringComposite
#print axioms SerrePositivity.KST.SConstruction.compositionStringComposite
#check @SerrePositivity.KST.SConstruction.compositionStringFirst
#print axioms SerrePositivity.KST.SConstruction.compositionStringFirst
#check @SerrePositivity.KST.SConstruction.compositionStringSecond
#print axioms SerrePositivity.KST.SConstruction.compositionStringSecond
#check @SerrePositivity.KST.SConstruction.compositionStringComposite_direct
#print axioms SerrePositivity.KST.SConstruction.compositionStringComposite_direct
#check @SerrePositivity.KST.SConstruction.compositionStringFirst_direct
#print axioms SerrePositivity.KST.SConstruction.compositionStringFirst_direct
#check @SerrePositivity.KST.SConstruction.compositionStringSecond_direct
#print axioms SerrePositivity.KST.SConstruction.compositionStringSecond_direct
#check @SerrePositivity.KST.SConstruction.compositionStringDirect_anodyne
#print axioms SerrePositivity.KST.SConstruction.compositionStringDirect_anodyne
#check @SerrePositivity.KST.SConstruction.specifiedTriangleFamilyBoundaryData
#print axioms SerrePositivity.KST.SConstruction.specifiedTriangleFamilyBoundaryData
#check @SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleMap
#print axioms SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleMap
#check @SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleMap_boundary
#print axioms SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleMap_boundary
#check @SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleMap_first
#print axioms SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleMap_first
#check @SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleMap_second
#print axioms SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleMap_second
#check @SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleMap_composite
#print axioms SerrePositivity.KST.SConstruction.relativeSpecifiedTriangleMap_composite
#check @SerrePositivity.KST.SConstruction.constantFamilyHomotopyWhisker
#print axioms SerrePositivity.KST.SConstruction.constantFamilyHomotopyWhisker
#check @SerrePositivity.KST.SConstruction.constantFamilyHomotopyWhisker_boundary
#print axioms SerrePositivity.KST.SConstruction.constantFamilyHomotopyWhisker_boundary
#check @SerrePositivity.KST.SConstruction.constantHomotopy_endpoints_of_specifiedPoint
#print axioms SerrePositivity.KST.SConstruction.constantHomotopy_endpoints_of_specifiedPoint
#check @SerrePositivity.KST.SConstruction.specifiedPointConstantHomotopy
#print axioms SerrePositivity.KST.SConstruction.specifiedPointConstantHomotopy
#check @SerrePositivity.KST.SConstruction.kCompositionNativeCylindersPointedCategory
#print axioms SerrePositivity.KST.SConstruction.kCompositionNativeCylindersPointedCategory
#check @SerrePositivity.KST.SConstruction.kKanCompositionFirstNativeCylinder
#print axioms SerrePositivity.KST.SConstruction.kKanCompositionFirstNativeCylinder
#check @SerrePositivity.KST.SConstruction.kKanCompositionFirstNativeCylinder_boundary
#print axioms SerrePositivity.KST.SConstruction.kKanCompositionFirstNativeCylinder_boundary
#check @SerrePositivity.KST.SConstruction.kKanCompositionSecondNativeCylinder
#print axioms SerrePositivity.KST.SConstruction.kKanCompositionSecondNativeCylinder
#check @SerrePositivity.KST.SConstruction.kKanCompositionSecondNativeCylinder_boundary
#print axioms SerrePositivity.KST.SConstruction.kKanCompositionSecondNativeCylinder_boundary
#check @SerrePositivity.KST.SConstruction.kKanCompositionCompositeNativeCylinder
#print axioms SerrePositivity.KST.SConstruction.kKanCompositionCompositeNativeCylinder
#check @SerrePositivity.KST.SConstruction.kKanCompositionCompositeNativeCylinder_boundary
#print axioms SerrePositivity.KST.SConstruction.kKanCompositionCompositeNativeCylinder_boundary
#check @SerrePositivity.KST.SConstruction.kCompositionNativeFamiliesPointedCategory
#print axioms SerrePositivity.KST.SConstruction.kCompositionNativeFamiliesPointedCategory
#check @SerrePositivity.KST.SConstruction.kKanCompositionFirstNativeFamily
#print axioms SerrePositivity.KST.SConstruction.kKanCompositionFirstNativeFamily
#check @SerrePositivity.KST.SConstruction.kKanCompositionSecondNativeFamily
#print axioms SerrePositivity.KST.SConstruction.kKanCompositionSecondNativeFamily
#check @SerrePositivity.KST.SConstruction.kKanCompositionCompositeNativeFamily
#print axioms SerrePositivity.KST.SConstruction.kKanCompositionCompositeNativeFamily
#check @SerrePositivity.KST.SConstruction.kKanCompositionFirstNativeFamily_boundary
#print axioms SerrePositivity.KST.SConstruction.kKanCompositionFirstNativeFamily_boundary
#check @SerrePositivity.KST.SConstruction.kKanCompositionSecondNativeFamily_boundary
#print axioms SerrePositivity.KST.SConstruction.kKanCompositionSecondNativeFamily_boundary
#check @SerrePositivity.KST.SConstruction.kKanCompositionCompositeNativeFamily_boundary
#print axioms SerrePositivity.KST.SConstruction.kKanCompositionCompositeNativeFamily_boundary
#check @SerrePositivity.KST.SConstruction.kCompositionNativeTrianglesPointedCategory
#print axioms SerrePositivity.KST.SConstruction.kCompositionNativeTrianglesPointedCategory
#check @SerrePositivity.KST.SConstruction.kCompositionNativeTrianglesKan
#print axioms SerrePositivity.KST.SConstruction.kCompositionNativeTrianglesKan
#check @SerrePositivity.KST.SConstruction.kKanCompositionNativeTriangle
#print axioms SerrePositivity.KST.SConstruction.kKanCompositionNativeTriangle
#check @SerrePositivity.KST.SConstruction.kKanCompositionNativeTriangle_boundary
#print axioms SerrePositivity.KST.SConstruction.kKanCompositionNativeTriangle_boundary
#check @SerrePositivity.KST.SConstruction.kKanCompositionNativeTriangle_first
#print axioms SerrePositivity.KST.SConstruction.kKanCompositionNativeTriangle_first
#check @SerrePositivity.KST.SConstruction.kKanCompositionNativeTriangle_second
#print axioms SerrePositivity.KST.SConstruction.kKanCompositionNativeTriangle_second
#check @SerrePositivity.KST.SConstruction.kKanCompositionNativeTriangle_composite
#print axioms SerrePositivity.KST.SConstruction.kKanCompositionNativeTriangle_composite
#check @SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTrianglesPointedCategory
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTrianglesPointedCategory
#check @SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle
#check @SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle_boundary
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle_boundary
#check @SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle_first
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle_first
#check @SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle_second
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle_second
#check @SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle_composite
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle_composite

-- 元の全比較三角形と保存済み補正の全 trace の接続。
#check @SerrePositivity.KST.SConstruction.compositionStringPair
#print axioms SerrePositivity.KST.SConstruction.compositionStringPair
#check @SerrePositivity.KST.SConstruction.compositionStringPair_first
#print axioms SerrePositivity.KST.SConstruction.compositionStringPair_first
#check @SerrePositivity.KST.SConstruction.compositionStringPair_second
#print axioms SerrePositivity.KST.SConstruction.compositionStringPair_second
#check @SerrePositivity.KST.SConstruction.pointedMapping_pre_comp
#print axioms SerrePositivity.KST.SConstruction.pointedMapping_pre_comp
#check @SerrePositivity.KST.SConstruction.pointedMapping_pre_suspension_comp
#print axioms SerrePositivity.KST.SConstruction.pointedMapping_pre_suspension_comp
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeTraceFacesPointedCategory
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeTraceFacesPointedCategory
#check @SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle_first_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle_first_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle_composite_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle_composite_trace
#check @SerrePositivity.KST.SConstruction.originalCompatibilityCylinderPointedCategory
#print axioms SerrePositivity.KST.SConstruction.originalCompatibilityCylinderPointedCategory
#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeCompatibilityAt_raw
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeCompatibilityAt_raw
#check @SerrePositivity.KST.SConstruction.nativeSecondTraceFacePointedCategory
#print axioms SerrePositivity.KST.SConstruction.nativeSecondTraceFacePointedCategory
#check @SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeSecondCylinder_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeSecondCylinder_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle_second_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle_second_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeSecondCompatibilityTransport
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeSecondCompatibilityTransport
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeSecondCompatibilityTransport_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeSecondCompatibilityTransport_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeSecondCompatibilityTransport_zero_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeSecondCompatibilityTransport_zero_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle_second_zero
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositionNativeTriangle_second_zero
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeCorrectionChain
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeCorrectionChain
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeCorrectionChain_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeCorrectionChain_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeCorrectionChain_zero_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeCorrectionChain_zero_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeCorrectionChain_zero
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeCorrectionChain_zero
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeCorrectionChain_projection_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeCorrectionChain_projection_trace

-- 元の全三角形と全交換セルを保持する実比較複体・両側の全 trace。
#check @SerrePositivity.KST.SConstruction.CylinderCellWalk
#print axioms SerrePositivity.KST.SConstruction.CylinderCellWalk
#check @SerrePositivity.KST.SConstruction.cylinderCellWalkMap
#print axioms SerrePositivity.KST.SConstruction.cylinderCellWalkMap
#check @SerrePositivity.KST.SConstruction.CylinderCellWalk.nil
#print axioms SerrePositivity.KST.SConstruction.CylinderCellWalk.nil
#check @SerrePositivity.KST.SConstruction.CylinderCellWalk.cons
#print axioms SerrePositivity.KST.SConstruction.CylinderCellWalk.cons
#check @SerrePositivity.KST.SConstruction.FamilyChainPastingData
#print axioms SerrePositivity.KST.SConstruction.FamilyChainPastingData
#check @SerrePositivity.KST.SConstruction.familyChainPasting
#print axioms SerrePositivity.KST.SConstruction.familyChainPasting
#check @SerrePositivity.KST.SConstruction.FamilyChainPastingData.mk
#print axioms SerrePositivity.KST.SConstruction.FamilyChainPastingData.mk
#check @SerrePositivity.KST.SConstruction.FamilyChainPastingData.domain
#print axioms SerrePositivity.KST.SConstruction.FamilyChainPastingData.domain
#check @SerrePositivity.KST.SConstruction.FamilyChainPastingData.source
#print axioms SerrePositivity.KST.SConstruction.FamilyChainPastingData.source
#check @SerrePositivity.KST.SConstruction.FamilyChainPastingData.target
#print axioms SerrePositivity.KST.SConstruction.FamilyChainPastingData.target
#check @SerrePositivity.KST.SConstruction.FamilyChainPastingData.cells
#print axioms SerrePositivity.KST.SConstruction.FamilyChainPastingData.cells
#check @SerrePositivity.KST.SConstruction.FamilyChainPastingData.walk
#print axioms SerrePositivity.KST.SConstruction.FamilyChainPastingData.walk
#check @SerrePositivity.KST.SConstruction.FamilyChainPastingData.map
#print axioms SerrePositivity.KST.SConstruction.FamilyChainPastingData.map
#check @SerrePositivity.KST.SConstruction.FamilyChainPastingData.source_eq
#print axioms SerrePositivity.KST.SConstruction.FamilyChainPastingData.source_eq
#check @SerrePositivity.KST.SConstruction.FamilyChainPastingData.target_eq
#print axioms SerrePositivity.KST.SConstruction.FamilyChainPastingData.target_eq
#check @SerrePositivity.KST.SConstruction.FamilyChainPastingData.cells_eq
#print axioms SerrePositivity.KST.SConstruction.FamilyChainPastingData.cells_eq
#check @SerrePositivity.KST.SConstruction.triangleCylinderPastingDomain
#print axioms SerrePositivity.KST.SConstruction.triangleCylinderPastingDomain
#check @SerrePositivity.KST.SConstruction.triangleCylinderPastingTriangle
#print axioms SerrePositivity.KST.SConstruction.triangleCylinderPastingTriangle
#check @SerrePositivity.KST.SConstruction.triangleCylinderPastingStrip
#print axioms SerrePositivity.KST.SConstruction.triangleCylinderPastingStrip
#check @SerrePositivity.KST.SConstruction.triangleCylinderPastingMap
#print axioms SerrePositivity.KST.SConstruction.triangleCylinderPastingMap
#check @SerrePositivity.KST.SConstruction.triangleCylinderPasting_shared
#print axioms SerrePositivity.KST.SConstruction.triangleCylinderPasting_shared
#check @SerrePositivity.KST.SConstruction.triangleCylinderPastingMap_triangle
#print axioms SerrePositivity.KST.SConstruction.triangleCylinderPastingMap_triangle
#check @SerrePositivity.KST.SConstruction.triangleCylinderPastingMap_strip
#print axioms SerrePositivity.KST.SConstruction.triangleCylinderPastingMap_strip
#check @SerrePositivity.KST.SConstruction.triangleCylinderPastingMap_target
#print axioms SerrePositivity.KST.SConstruction.triangleCylinderPastingMap_target
#check @SerrePositivity.KST.SConstruction.triangleCylinderPastingCells
#print axioms SerrePositivity.KST.SConstruction.triangleCylinderPastingCells
#check @SerrePositivity.KST.SConstruction.triangleCylinderPastingWalk
#print axioms SerrePositivity.KST.SConstruction.triangleCylinderPastingWalk
#check @SerrePositivity.KST.SConstruction.triangleCylinderPastingMap_cells
#print axioms SerrePositivity.KST.SConstruction.triangleCylinderPastingMap_cells
#check @SerrePositivity.KST.SConstruction.familySquareClockSwap
#print axioms SerrePositivity.KST.SConstruction.familySquareClockSwap
#check @SerrePositivity.KST.SConstruction.familyInterchangeSquare_clockSwap
#print axioms SerrePositivity.KST.SConstruction.familyInterchangeSquare_clockSwap
#check @SerrePositivity.KST.SConstruction.familyInterchangeCylinderChain_trace_clockSwap
#print axioms SerrePositivity.KST.SConstruction.familyInterchangeCylinderChain_trace_clockSwap
#check @SerrePositivity.KST.SConstruction.familySquareClockSwap_restrict
#print axioms SerrePositivity.KST.SConstruction.familySquareClockSwap_restrict
#check @SerrePositivity.KST.SConstruction.familySquareClockSwap_second_zero
#print axioms SerrePositivity.KST.SConstruction.familySquareClockSwap_second_zero
#check @SerrePositivity.KST.SConstruction.familySquareClockSwap_first_zero
#print axioms SerrePositivity.KST.SConstruction.familySquareClockSwap_first_zero
#check @SerrePositivity.KST.SConstruction.familySquareClockSwap_second_one
#print axioms SerrePositivity.KST.SConstruction.familySquareClockSwap_second_one
#check @SerrePositivity.KST.SConstruction.familySquareClockSwap_first_one
#print axioms SerrePositivity.KST.SConstruction.familySquareClockSwap_first_one
#check @SerrePositivity.KST.SConstruction.familySquareClockSwap_first_zero_restrict
#print axioms SerrePositivity.KST.SConstruction.familySquareClockSwap_first_zero_restrict
#check @SerrePositivity.KST.SConstruction.familySquareClockSwap_first_one_restrict
#print axioms SerrePositivity.KST.SConstruction.familySquareClockSwap_first_one_restrict
#check @SerrePositivity.KST.SConstruction.familySquareClockSwap_first_zero_restrict_assoc
#print axioms SerrePositivity.KST.SConstruction.familySquareClockSwap_first_zero_restrict_assoc
#check @SerrePositivity.KST.SConstruction.familySquareClockSwap_first_one_restrict_assoc
#print axioms SerrePositivity.KST.SConstruction.familySquareClockSwap_first_one_restrict_assoc
#check @SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondCompatibilityTransport_square_cells
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompositeSecondCompatibilityTransport_square_cells
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeSecondCompatibilityTransport_square_cells
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeSecondCompatibilityTransport_square_cells
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingDomain
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingDomain
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingTriangle
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingTriangle
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingCells
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingCells
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingWalk
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingWalk
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingTarget
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingTarget
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_triangle
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_triangle
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_target
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_target
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_cells
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_cells
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_first
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_first
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_composite
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_composite
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_zero_cells
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_zero_cells
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePasting_zero_cells
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePasting_zero_cells
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_cells_zero_faces
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_cells_zero_faces
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_cells_zero_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_cells_zero_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_cells_one_faces
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_cells_one_faces
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_cells_one_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_cells_one_trace
#check @SerrePositivity.KST.SConstruction.nativePreviousTracePointedCategory
#print axioms SerrePositivity.KST.SConstruction.nativePreviousTracePointedCategory
#check @SerrePositivity.KST.SConstruction.monicKPrismCompatibilityInterchangeTrace_one_step
#print axioms SerrePositivity.KST.SConstruction.monicKPrismCompatibilityInterchangeTrace_one_step
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_cells_one_previous_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_cells_one_previous_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePasting_previous_full_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePasting_previous_full_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePasting_projected_full_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePasting_projected_full_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePasting_original_full_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePasting_original_full_trace
#check @SerrePositivity.KST.SConstruction.endpointFixedEdgeTransport
#print axioms SerrePositivity.KST.SConstruction.endpointFixedEdgeTransport
#check @SerrePositivity.KST.SConstruction.endpointFixedEdgeSquare
#print axioms SerrePositivity.KST.SConstruction.endpointFixedEdgeSquare
#check @SerrePositivity.KST.SConstruction.endpointFixedEdgeSquare_zero
#print axioms SerrePositivity.KST.SConstruction.endpointFixedEdgeSquare_zero
#check @SerrePositivity.KST.SConstruction.endpointFixedEdgeSquare_one
#print axioms SerrePositivity.KST.SConstruction.endpointFixedEdgeSquare_one
#check @SerrePositivity.KST.SConstruction.endpointFixedEdgeSquare_source
#print axioms SerrePositivity.KST.SConstruction.endpointFixedEdgeSquare_source
#check @SerrePositivity.KST.SConstruction.endpointFixedEdgeSquare_target
#print axioms SerrePositivity.KST.SConstruction.endpointFixedEdgeSquare_target
#check @SerrePositivity.KST.SConstruction.endpointFixedEdgeSquare_triangle
#print axioms SerrePositivity.KST.SConstruction.endpointFixedEdgeSquare_triangle
#check @SerrePositivity.KST.SConstruction.endpointFixedEdgeSquare_vertical_zero
#print axioms SerrePositivity.KST.SConstruction.endpointFixedEdgeSquare_vertical_zero
#check @SerrePositivity.KST.SConstruction.endpointFixedEdgeSquare_vertical_one
#print axioms SerrePositivity.KST.SConstruction.endpointFixedEdgeSquare_vertical_one
#check @SerrePositivity.KST.SConstruction.familyChainCompositeClass
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositeClass
#check @SerrePositivity.KST.SConstruction.familyChainCompositionWitness_class
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositionWitness_class
#check @SerrePositivity.KST.SConstruction.familyChainCompositionWitness_class_eq
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositionWitness_class_eq
#check @SerrePositivity.KST.SConstruction.familyChainCompositionComparisonTriangle
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositionComparisonTriangle
#check @SerrePositivity.KST.SConstruction.FamilyChainCompositeData
#print axioms SerrePositivity.KST.SConstruction.FamilyChainCompositeData
#check @SerrePositivity.KST.SConstruction.familyChainCompositeData
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositeData
#check @SerrePositivity.KST.SConstruction.familyChainCompositeData_trace
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositeData_trace
#check @SerrePositivity.KST.SConstruction.familyChainCompositionWitness_constant_of_trace_nil
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositionWitness_constant_of_trace_nil
#check @SerrePositivity.KST.SConstruction.familyChainCompositeData_constant_of_trace_nil
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositeData_constant_of_trace_nil
#check @SerrePositivity.KST.SConstruction.familyChainCompositionComparisonSquare
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositionComparisonSquare
#check @SerrePositivity.KST.SConstruction.familyChainCompositionComparison
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositionComparison
#check @SerrePositivity.KST.SConstruction.familyChainCompositionComparison_source
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositionComparison_source
#check @SerrePositivity.KST.SConstruction.familyChainCompositionComparison_target
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositionComparison_target
#check @SerrePositivity.KST.SConstruction.FamilyChainCompositionWitness
#print axioms SerrePositivity.KST.SConstruction.FamilyChainCompositionWitness
#check @SerrePositivity.KST.SConstruction.familyChainCompositionInputTrace
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositionInputTrace
#check @SerrePositivity.KST.SConstruction.familyChainCompositionInputTrace_eq
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositionInputTrace_eq
#check @SerrePositivity.KST.SConstruction.familyChainCompositionTriangles
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositionTriangles
#check @SerrePositivity.KST.SConstruction.KanMappingComposition
#print axioms SerrePositivity.KST.SConstruction.KanMappingComposition
#check @SerrePositivity.KST.SConstruction.kanMappingComposition
#print axioms SerrePositivity.KST.SConstruction.kanMappingComposition
#check @SerrePositivity.KST.SConstruction.mappingSquareUncurry
#print axioms SerrePositivity.KST.SConstruction.mappingSquareUncurry
#check @SerrePositivity.KST.SConstruction.mappingSquareUncurry_zero
#print axioms SerrePositivity.KST.SConstruction.mappingSquareUncurry_zero
#check @SerrePositivity.KST.SConstruction.mappingSquareUncurry_one
#print axioms SerrePositivity.KST.SConstruction.mappingSquareUncurry_one
#check @SerrePositivity.KST.SConstruction.mappingSquareUncurry_source
#print axioms SerrePositivity.KST.SConstruction.mappingSquareUncurry_source
#check @SerrePositivity.KST.SConstruction.mappingSquareUncurry_target
#print axioms SerrePositivity.KST.SConstruction.mappingSquareUncurry_target
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeCorrectionData
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeCorrectionData
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeCorrectionData_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeCorrectionData_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeCorrectionData_zero
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeCorrectionData_zero
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeSecondCompatibilityData
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeSecondCompatibilityData
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeSecondCompatibilityData_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeSecondCompatibilityData_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeSecondCompatibilityData_zero
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeSecondCompatibilityData_zero
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectCorrectionChain
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectCorrectionChain
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectCorrectionChain_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectCorrectionChain_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectCorrectionChain_zero_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectCorrectionChain_zero_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectCorrectionData
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectCorrectionData
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectCorrectionData_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectCorrectionData_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectCorrectionData_zero
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectCorrectionData_zero
#check @SerrePositivity.KST.SConstruction.KanMappingComposition.mk
#print axioms SerrePositivity.KST.SConstruction.KanMappingComposition.mk
#check @SerrePositivity.KST.SConstruction.KanMappingComposition.edge
#print axioms SerrePositivity.KST.SConstruction.KanMappingComposition.edge
#check @SerrePositivity.KST.SConstruction.KanMappingComposition.triangle
#print axioms SerrePositivity.KST.SConstruction.KanMappingComposition.triangle
#check @SerrePositivity.KST.SConstruction.FamilyChainCompositionWitness.nil
#print axioms SerrePositivity.KST.SConstruction.FamilyChainCompositionWitness.nil
#check @SerrePositivity.KST.SConstruction.FamilyChainCompositionWitness.cons
#print axioms SerrePositivity.KST.SConstruction.FamilyChainCompositionWitness.cons
#check @SerrePositivity.KST.SConstruction.FamilyChainCompositeData.mk
#print axioms SerrePositivity.KST.SConstruction.FamilyChainCompositeData.mk
#check @SerrePositivity.KST.SConstruction.FamilyChainCompositeData.homotopy
#print axioms SerrePositivity.KST.SConstruction.FamilyChainCompositeData.homotopy
#check @SerrePositivity.KST.SConstruction.FamilyChainCompositeData.witness
#print axioms SerrePositivity.KST.SConstruction.FamilyChainCompositeData.witness
#check @SerrePositivity.KST.SConstruction.familyChainCompositeClass_append
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositeClass_append
#check @SerrePositivity.KST.SConstruction.familyChainCompositeClass_single
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositeClass_single
#check @SerrePositivity.KST.SConstruction.familyChainCompositeClass_map
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositeClass_map
#check @SerrePositivity.KST.SConstruction.familyChainCompositeClass_precomp
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositeClass_precomp
#check @SerrePositivity.KST.SConstruction.familyHomotopySquareBoundary
#print axioms SerrePositivity.KST.SConstruction.familyHomotopySquareBoundary
#check @SerrePositivity.KST.SConstruction.familyHomotopySquare_class
#print axioms SerrePositivity.KST.SConstruction.familyHomotopySquare_class
#check @SerrePositivity.KST.SConstruction.familyChainRectangle_class
#print axioms SerrePositivity.KST.SConstruction.familyChainRectangle_class
#check @SerrePositivity.KST.SConstruction.familyChainRectangleLeft
#print axioms SerrePositivity.KST.SConstruction.familyChainRectangleLeft
#check @SerrePositivity.KST.SConstruction.familyChainRectangleRight
#print axioms SerrePositivity.KST.SConstruction.familyChainRectangleRight
#check @SerrePositivity.KST.SConstruction.familyChainRectangleLeft_trace
#print axioms SerrePositivity.KST.SConstruction.familyChainRectangleLeft_trace
#check @SerrePositivity.KST.SConstruction.familyChainRectangleRight_trace
#print axioms SerrePositivity.KST.SConstruction.familyChainRectangleRight_trace
#check @SerrePositivity.KST.SConstruction.familyChainRectangleLeft_class_eq
#print axioms SerrePositivity.KST.SConstruction.familyChainRectangleLeft_class_eq
#check @SerrePositivity.KST.SConstruction.familyChainRectangle_composite_class_eq
#print axioms SerrePositivity.KST.SConstruction.familyChainRectangle_composite_class_eq
#check @SerrePositivity.KST.SConstruction.familyChainRectangleComparison
#print axioms SerrePositivity.KST.SConstruction.familyChainRectangleComparison
#check @SerrePositivity.KST.SConstruction.familyChainRectangleComparison_source
#print axioms SerrePositivity.KST.SConstruction.familyChainRectangleComparison_source
#check @SerrePositivity.KST.SConstruction.familyChainRectangleComparison_target
#print axioms SerrePositivity.KST.SConstruction.familyChainRectangleComparison_target
#check @SerrePositivity.KST.SConstruction.familyHomotopyChainTrace_injective
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainTrace_injective
#check @SerrePositivity.KST.SConstruction.familyChainCompositeClass_eq_of_trace
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositeClass_eq_of_trace
#check @SerrePositivity.KST.SConstruction.familyHomotopyChainTrace_target_eq
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainTrace_target_eq
#check @SerrePositivity.KST.SConstruction.FamilyChainSplitData
#print axioms SerrePositivity.KST.SConstruction.FamilyChainSplitData
#check @SerrePositivity.KST.SConstruction.familyChainSplit
#print axioms SerrePositivity.KST.SConstruction.familyChainSplit
#check @SerrePositivity.KST.SConstruction.familyChainPrefixTail
#print axioms SerrePositivity.KST.SConstruction.familyChainPrefixTail
#check @SerrePositivity.KST.SConstruction.familyChainPrefixTail_trace
#print axioms SerrePositivity.KST.SConstruction.familyChainPrefixTail_trace
#check @SerrePositivity.KST.SConstruction.familyCylinderClassComparisonTriangle
#print axioms SerrePositivity.KST.SConstruction.familyCylinderClassComparisonTriangle
#check @SerrePositivity.KST.SConstruction.familyCylinderClassComparison
#print axioms SerrePositivity.KST.SConstruction.familyCylinderClassComparison
#check @SerrePositivity.KST.SConstruction.familyCylinderClassComparison_source
#print axioms SerrePositivity.KST.SConstruction.familyCylinderClassComparison_source
#check @SerrePositivity.KST.SConstruction.familyCylinderClassComparison_target
#print axioms SerrePositivity.KST.SConstruction.familyCylinderClassComparison_target
#check @SerrePositivity.KST.SConstruction.familyCylinder
#print axioms SerrePositivity.KST.SConstruction.familyCylinder
#check @SerrePositivity.KST.SConstruction.familySquareCurry
#print axioms SerrePositivity.KST.SConstruction.familySquareCurry
#check @SerrePositivity.KST.SConstruction.mappingSquareUncurry_familySquareCurry
#print axioms SerrePositivity.KST.SConstruction.mappingSquareUncurry_familySquareCurry
#check @SerrePositivity.KST.SConstruction.familySquareCurry_zero
#print axioms SerrePositivity.KST.SConstruction.familySquareCurry_zero
#check @SerrePositivity.KST.SConstruction.familySquareCurry_one
#print axioms SerrePositivity.KST.SConstruction.familySquareCurry_one
#check @SerrePositivity.KST.SConstruction.familySquareCurry_source
#print axioms SerrePositivity.KST.SConstruction.familySquareCurry_source
#check @SerrePositivity.KST.SConstruction.familySquareCurry_target
#print axioms SerrePositivity.KST.SConstruction.familySquareCurry_target
#check @SerrePositivity.KST.SConstruction.familyTriangleCorner_middle
#print axioms SerrePositivity.KST.SConstruction.familyTriangleCorner_middle
#check @SerrePositivity.KST.SConstruction.familyTriangleCorner_source
#print axioms SerrePositivity.KST.SConstruction.familyTriangleCorner_source
#check @SerrePositivity.KST.SConstruction.familyTriangleCorner_target
#print axioms SerrePositivity.KST.SConstruction.familyTriangleCorner_target
#check @SerrePositivity.KST.SConstruction.familyTriangleFirst
#print axioms SerrePositivity.KST.SConstruction.familyTriangleFirst
#check @SerrePositivity.KST.SConstruction.familyTriangleDirect
#print axioms SerrePositivity.KST.SConstruction.familyTriangleDirect
#check @SerrePositivity.KST.SConstruction.familyTriangleCurry_face
#print axioms SerrePositivity.KST.SConstruction.familyTriangleCurry_face
#check @SerrePositivity.KST.SConstruction.familyTriangleCompStruct
#print axioms SerrePositivity.KST.SConstruction.familyTriangleCompStruct
#check @SerrePositivity.KST.SConstruction.familyTriangleCompStruct_map
#print axioms SerrePositivity.KST.SConstruction.familyTriangleCompStruct_map
#check @SerrePositivity.KST.SConstruction.familyTriangleStripDirect
#print axioms SerrePositivity.KST.SConstruction.familyTriangleStripDirect
#check @SerrePositivity.KST.SConstruction.familyTriangleStripProjected
#print axioms SerrePositivity.KST.SConstruction.familyTriangleStripProjected
#check @SerrePositivity.KST.SConstruction.familyTriangleStripDirect_trace
#print axioms SerrePositivity.KST.SConstruction.familyTriangleStripDirect_trace
#check @SerrePositivity.KST.SConstruction.familyTriangleStripProjected_trace
#print axioms SerrePositivity.KST.SConstruction.familyTriangleStripProjected_trace
#check @SerrePositivity.KST.SConstruction.familyTriangleStrip_class
#print axioms SerrePositivity.KST.SConstruction.familyTriangleStrip_class
#check @SerrePositivity.KST.SConstruction.familyTriangleStrip_composite_class_eq
#print axioms SerrePositivity.KST.SConstruction.familyTriangleStrip_composite_class_eq
#check @SerrePositivity.KST.SConstruction.familyTriangleStripComparison
#print axioms SerrePositivity.KST.SConstruction.familyTriangleStripComparison
#check @SerrePositivity.KST.SConstruction.familyTriangleStripComparison_source
#print axioms SerrePositivity.KST.SConstruction.familyTriangleStripComparison_source
#check @SerrePositivity.KST.SConstruction.familyTriangleStripComparison_target
#print axioms SerrePositivity.KST.SConstruction.familyTriangleStripComparison_target
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDiskDirectPath
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDiskDirectPath
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDiskProjectedPath
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDiskProjectedPath
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_cells_transport_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePastingMap_cells_transport_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDiskDirectPath_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDiskDirectPath_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDiskProjectedPath_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDiskProjectedPath_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedCorrectionChain
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedCorrectionChain
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedCorrectionChain_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedCorrectionChain_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDiskProjectedPath_trace_ne_nil
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDiskProjectedPath_trace_ne_nil
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeSharedTail
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeSharedTail
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeSharedTail_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeSharedTail_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeFullDirectPath
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeFullDirectPath
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeFullProjectedPath
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeFullProjectedPath
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeFullProjectedPath_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeFullProjectedPath_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeFullDirectPath_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeFullDirectPath_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeFullPathComparison
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeFullPathComparison
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeFullPathComparison_source
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeFullPathComparison_source
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeFullPathComparison_target
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeFullPathComparison_target
#check @SerrePositivity.KST.SConstruction.FamilyChainSplitData.mk
#print axioms SerrePositivity.KST.SConstruction.FamilyChainSplitData.mk
#check @SerrePositivity.KST.SConstruction.FamilyChainSplitData.middle
#print axioms SerrePositivity.KST.SConstruction.FamilyChainSplitData.middle
#check @SerrePositivity.KST.SConstruction.FamilyChainSplitData.before
#print axioms SerrePositivity.KST.SConstruction.FamilyChainSplitData.before
#check @SerrePositivity.KST.SConstruction.FamilyChainSplitData.after
#print axioms SerrePositivity.KST.SConstruction.FamilyChainSplitData.after
#check @SerrePositivity.KST.SConstruction.FamilyChainSplitData.before_trace
#print axioms SerrePositivity.KST.SConstruction.FamilyChainSplitData.before_trace
#check @SerrePositivity.KST.SConstruction.FamilyChainSplitData.after_trace
#print axioms SerrePositivity.KST.SConstruction.FamilyChainSplitData.after_trace
#check @SerrePositivity.KST.SConstruction.familyHomotopyChainTrace_source_eq
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyChainTrace_source_eq
#check @SerrePositivity.KST.SConstruction.familyChainCompositeClass_transfer
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositeClass_transfer
#check @SerrePositivity.KST.SConstruction.familyCompStructRealization
#print axioms SerrePositivity.KST.SConstruction.familyCompStructRealization
#check @SerrePositivity.KST.SConstruction.familyCompStructRealization_first
#print axioms SerrePositivity.KST.SConstruction.familyCompStructRealization_first
#check @SerrePositivity.KST.SConstruction.familyCompStructRealization_second
#print axioms SerrePositivity.KST.SConstruction.familyCompStructRealization_second
#check @SerrePositivity.KST.SConstruction.familyCompStructRealization_direct
#print axioms SerrePositivity.KST.SConstruction.familyCompStructRealization_direct
#check @SerrePositivity.KST.SConstruction.familyHomotopyEndpointTransport
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyEndpointTransport
#check @SerrePositivity.KST.SConstruction.familyHomotopyEndpointTransport_h
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyEndpointTransport_h
#check @SerrePositivity.KST.SConstruction.familyChainCompositionWitness_postcomp_class
#print axioms SerrePositivity.KST.SConstruction.familyChainCompositionWitness_postcomp_class
#check @SerrePositivity.KST.SConstruction.familyCompositeClass_endpointTransport
#print axioms SerrePositivity.KST.SConstruction.familyCompositeClass_endpointTransport
#check @SerrePositivity.KST.SConstruction.FamilyCorrectionSpanData
#print axioms SerrePositivity.KST.SConstruction.FamilyCorrectionSpanData
#check @SerrePositivity.KST.SConstruction.familySpanComparisonData
#print axioms SerrePositivity.KST.SConstruction.familySpanComparisonData
#check @SerrePositivity.KST.SConstruction.familyCorrectionSpanData
#print axioms SerrePositivity.KST.SConstruction.familyCorrectionSpanData
#check @SerrePositivity.KST.SConstruction.familyCorrectionSpanData_constant
#print axioms SerrePositivity.KST.SConstruction.familyCorrectionSpanData_constant
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectRaw_condition
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectRaw_condition
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectPreviousStructureChain
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectPreviousStructureChain
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectPreviousStructureCylinder
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectPreviousStructureCylinder
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectProjectedStructureCylinder
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectProjectedStructureCylinder
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectProjectedStructureChain
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectProjectedStructureChain
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectStructureChain
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectStructureChain
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectCorrectionChain_projection_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectCorrectionChain_projection_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectStructureChain_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectStructureChain_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectPreviousStructureCylinder_class
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectPreviousStructureCylinder_class
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectProjectedStructureCylinder_class
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectProjectedStructureCylinder_class
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectStructureTriangle
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectStructureTriangle
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeLevelComparisonData
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeLevelComparisonData
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeLevelComparison
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeLevelComparison
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeLevelComparisonMap
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeLevelComparisonMap
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeLevelComparisonMap_first
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeLevelComparisonMap_first
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeLevelComparisonMap_comparison
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeLevelComparisonMap_comparison
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeLevelComparisonMap_composite
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeLevelComparisonMap_composite
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeLevelComparison_zero
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeLevelComparison_zero
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeRawComposition_condition
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeRawComposition_condition
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeOriginalCompatibility
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeOriginalCompatibility
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeOriginalCompatibility_h
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeOriginalCompatibility_h
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePreviousStructureChain
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePreviousStructureChain
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePreviousStructureCylinder
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePreviousStructureCylinder
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedStructureCylinder
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedStructureCylinder
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeStructureMap
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeStructureMap
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeStructureMap_first
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeStructureMap_first
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeStructureMap_previous
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeStructureMap_previous
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeStructureMap_projected
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeStructureMap_projected
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectStructureMap
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectStructureMap
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectStructureMap_first
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectStructureMap_first
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectStructureMap_previous
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectStructureMap_previous
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectStructureMap_projected
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectStructureMap_projected
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeStructureDirectChain
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeStructureDirectChain
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeStructureDirectChain_trace
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeStructureDirectChain_trace
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeStructureDirectChain_class
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeStructureDirectChain_class
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePreviousStructureCylinder_class
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePreviousStructureCylinder_class
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedStructureCylinder_class
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedStructureCylinder_class
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeStructureTriangle
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeStructureTriangle
#check @SerrePositivity.KST.SConstruction.FamilyCorrectionSpanData.mk
#print axioms SerrePositivity.KST.SConstruction.FamilyCorrectionSpanData.mk
#check @SerrePositivity.KST.SConstruction.FamilyCorrectionSpanData.homotopy
#print axioms SerrePositivity.KST.SConstruction.FamilyCorrectionSpanData.homotopy
#check @SerrePositivity.KST.SConstruction.FamilyCorrectionSpanData.triangle
#print axioms SerrePositivity.KST.SConstruction.FamilyCorrectionSpanData.triangle
#check @SerrePositivity.KST.SConstruction.FamilyCorrectionSpanData.realization
#print axioms SerrePositivity.KST.SConstruction.FamilyCorrectionSpanData.realization
#check @SerrePositivity.KST.SConstruction.FamilyCorrectionSpanData.realization_first
#print axioms SerrePositivity.KST.SConstruction.FamilyCorrectionSpanData.realization_first
#check @SerrePositivity.KST.SConstruction.FamilyCorrectionSpanData.realization_comparison
#print axioms SerrePositivity.KST.SConstruction.FamilyCorrectionSpanData.realization_comparison
#check @SerrePositivity.KST.SConstruction.FamilyCorrectionSpanData.realization_composite
#print axioms SerrePositivity.KST.SConstruction.FamilyCorrectionSpanData.realization_composite
#check @SerrePositivity.KST.SConstruction.familyCorrectionSpanDataOfEmpty
#print axioms SerrePositivity.KST.SConstruction.familyCorrectionSpanDataOfEmpty
#check @SerrePositivity.KST.SConstruction.fourTriangleComparison_class
#print axioms SerrePositivity.KST.SConstruction.fourTriangleComparison_class
#check @SerrePositivity.KST.SConstruction.fourTriangleComparisonTriangle
#print axioms SerrePositivity.KST.SConstruction.fourTriangleComparisonTriangle
#check @SerrePositivity.KST.SConstruction.fourTriangleComparisonSquare
#print axioms SerrePositivity.KST.SConstruction.fourTriangleComparisonSquare
#check @SerrePositivity.KST.SConstruction.familyCompStructImage
#print axioms SerrePositivity.KST.SConstruction.familyCompStructImage
#check @SerrePositivity.KST.SConstruction.familyCompStructImage_map
#print axioms SerrePositivity.KST.SConstruction.familyCompStructImage_map
#check @SerrePositivity.KST.SConstruction.familyCylinder_endpoints_of_boundary
#print axioms SerrePositivity.KST.SConstruction.familyCylinder_endpoints_of_boundary
#check @SerrePositivity.KST.SConstruction.exists_endpoint_preserving_cylinder_adjustment
#print axioms SerrePositivity.KST.SConstruction.exists_endpoint_preserving_cylinder_adjustment
#check @SerrePositivity.KST.SConstruction.CylinderEndpointAdjustmentData
#print axioms SerrePositivity.KST.SConstruction.CylinderEndpointAdjustmentData
#check @SerrePositivity.KST.SConstruction.cylinderEndpointAdjustmentData
#print axioms SerrePositivity.KST.SConstruction.cylinderEndpointAdjustmentData
#check @SerrePositivity.KST.SConstruction.familyCylinderVertex_zero
#print axioms SerrePositivity.KST.SConstruction.familyCylinderVertex_zero
#check @SerrePositivity.KST.SConstruction.familyCylinderVertex_one
#print axioms SerrePositivity.KST.SConstruction.familyCylinderVertex_one
#check @SerrePositivity.KST.SConstruction.familyCylinder_fixed_boundary
#print axioms SerrePositivity.KST.SConstruction.familyCylinder_fixed_boundary
#check @SerrePositivity.KST.SConstruction.familyCylinderTriangleComparison
#print axioms SerrePositivity.KST.SConstruction.familyCylinderTriangleComparison
#check @SerrePositivity.KST.SConstruction.familyCylinderTriangleComparison_source
#print axioms SerrePositivity.KST.SConstruction.familyCylinderTriangleComparison_source
#check @SerrePositivity.KST.SConstruction.familyCylinderTriangleComparison_target
#print axioms SerrePositivity.KST.SConstruction.familyCylinderTriangleComparison_target
#check @SerrePositivity.KST.SConstruction.nativeComparisonEndpointRestrictionFibration
#print axioms SerrePositivity.KST.SConstruction.nativeComparisonEndpointRestrictionFibration
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonAdjustmentData
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonAdjustmentData
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonAdjustmentData_projection
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonAdjustmentData_projection
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonAdjustmentData_boundary
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonAdjustmentData_boundary
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonAdjustmentData_comparison_projection
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonAdjustmentData_comparison_projection
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonCompatibilityTriangle
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonCompatibilityTriangle
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonCompatibility
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonCompatibility
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonCompatibility_zero
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonCompatibility_zero
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonCompatibility_one
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonCompatibility_one
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonCompatibility_source
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonCompatibility_source
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonCompatibility_target
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeComparisonCompatibility_target
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePreviousComparison
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePreviousComparison
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedComparison
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedComparison
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePreviousComparison_h
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePreviousComparison_h
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePreviousComparisonTriangle
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePreviousComparisonTriangle
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedComparisonTriangle
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedComparisonTriangle
#check @SerrePositivity.KST.SConstruction.monicKPrismNativePreviousComparisonTriangle_map
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativePreviousComparisonTriangle_map
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedComparisonTriangle_map
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedComparisonTriangle_map
#check @SerrePositivity.KST.SConstruction.CylinderEndpointAdjustmentData.mk
#print axioms SerrePositivity.KST.SConstruction.CylinderEndpointAdjustmentData.mk
#check @SerrePositivity.KST.SConstruction.CylinderEndpointAdjustmentData.val
#print axioms SerrePositivity.KST.SConstruction.CylinderEndpointAdjustmentData.val
#check @SerrePositivity.KST.SConstruction.CylinderEndpointAdjustmentData.projection
#print axioms SerrePositivity.KST.SConstruction.CylinderEndpointAdjustmentData.projection
#check @SerrePositivity.KST.SConstruction.CylinderEndpointAdjustmentData.comparison
#print axioms SerrePositivity.KST.SConstruction.CylinderEndpointAdjustmentData.comparison
#check @SerrePositivity.KST.SConstruction.CylinderEndpointAdjustmentData.boundary
#print axioms SerrePositivity.KST.SConstruction.CylinderEndpointAdjustmentData.boundary
#check @SerrePositivity.KST.SConstruction.CylinderEndpointAdjustmentData.comparison_projection
#print axioms SerrePositivity.KST.SConstruction.CylinderEndpointAdjustmentData.comparison_projection
#check @SerrePositivity.KST.SConstruction.cylinderBoundaryAdjustmentData
#print axioms SerrePositivity.KST.SConstruction.cylinderBoundaryAdjustmentData
#check @SerrePositivity.KST.SConstruction.fixedBoundaryMappingEdge_image
#print axioms SerrePositivity.KST.SConstruction.fixedBoundaryMappingEdge_image
#check @SerrePositivity.KST.SConstruction.FixedBoundaryCompositionData
#print axioms SerrePositivity.KST.SConstruction.FixedBoundaryCompositionData
#check @SerrePositivity.KST.SConstruction.fixedBoundaryCompositionData
#print axioms SerrePositivity.KST.SConstruction.fixedBoundaryCompositionData
#check @SerrePositivity.KST.SConstruction.fixedBoundaryMappingSpace
#print axioms SerrePositivity.KST.SConstruction.fixedBoundaryMappingSpace
#check @SerrePositivity.KST.SConstruction.fixedBoundaryMappingSpaceι
#print axioms SerrePositivity.KST.SConstruction.fixedBoundaryMappingSpaceι
#check @SerrePositivity.KST.SConstruction.fixedBoundaryMappingSpace_kanComplex
#print axioms SerrePositivity.KST.SConstruction.fixedBoundaryMappingSpace_kanComplex
#check @SerrePositivity.KST.SConstruction.fixedBoundaryMappingVertex
#print axioms SerrePositivity.KST.SConstruction.fixedBoundaryMappingVertex
#check @SerrePositivity.KST.SConstruction.fixedBoundaryHomotopy_curry
#print axioms SerrePositivity.KST.SConstruction.fixedBoundaryHomotopy_curry
#check @SerrePositivity.KST.SConstruction.fixedBoundaryMappingPath
#print axioms SerrePositivity.KST.SConstruction.fixedBoundaryMappingPath
#check @SerrePositivity.KST.SConstruction.fixedBoundaryMappingPath_ι
#print axioms SerrePositivity.KST.SConstruction.fixedBoundaryMappingPath_ι
#check @SerrePositivity.KST.SConstruction.fixedBoundaryMappingEdge
#print axioms SerrePositivity.KST.SConstruction.fixedBoundaryMappingEdge
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectBFFamily
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectBFFamily
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeBFFamily
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeBFFamily
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectBFFamily_projection
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectBFFamily_projection
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeBFFamily_projection
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeBFFamily_projection
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedRawComparison
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedRawComparison
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedRawComparison_h
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeProjectedRawComparison_h
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeBFComparisonBoundaryData
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeBFComparisonBoundaryData
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeBFComparisonData
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeBFComparisonData
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeBFComparisonData_projection
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeBFComparisonData_projection
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeBFComparisonData_boundary
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeBFComparisonData_boundary
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeRawCompatibility
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeRawCompatibility
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeRawCompatibility_h
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeRawCompatibility_h
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeRawCompatibility_boundary
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeRawCompatibility_boundary
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeCumulativeComparisonStage
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeCumulativeComparisonStage
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeRawComparison
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeRawComparison
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeRawComparison_evaluation
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeRawComparison_evaluation
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeRawComparison_zero
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeRawComparison_zero
#check @SerrePositivity.KST.SConstruction.familyBoundaryMap_post
#print axioms SerrePositivity.KST.SConstruction.familyBoundaryMap_post
#check @SerrePositivity.KST.SConstruction.familyHomotopyOfBoundary
#print axioms SerrePositivity.KST.SConstruction.familyHomotopyOfBoundary
#check @SerrePositivity.KST.SConstruction.rawHomotopyLiftData
#print axioms SerrePositivity.KST.SConstruction.rawHomotopyLiftData
#check @SerrePositivity.KST.SConstruction.prescribedRawHomotopyLiftData
#print axioms SerrePositivity.KST.SConstruction.prescribedRawHomotopyLiftData
#check @SerrePositivity.KST.SConstruction.rawComparisonRectificationMap
#print axioms SerrePositivity.KST.SConstruction.rawComparisonRectificationMap
#check @SerrePositivity.KST.SConstruction.rawComparisonRectificationMap_evaluation
#print axioms SerrePositivity.KST.SConstruction.rawComparisonRectificationMap_evaluation
#check @SerrePositivity.KST.SConstruction.rawComparisonRectification
#print axioms SerrePositivity.KST.SConstruction.rawComparisonRectification
#check @SerrePositivity.KST.SConstruction.rawComparisonRectification_zero
#print axioms SerrePositivity.KST.SConstruction.rawComparisonRectification_zero
#check @SerrePositivity.KST.SConstruction.RawComparisonStage
#print axioms SerrePositivity.KST.SConstruction.RawComparisonStage
#check @SerrePositivity.KST.SConstruction.rawComparisonBase
#print axioms SerrePositivity.KST.SConstruction.rawComparisonBase
#check @SerrePositivity.KST.SConstruction.rawComparisonRestrictionFibration
#print axioms SerrePositivity.KST.SConstruction.rawComparisonRestrictionFibration
#check @SerrePositivity.KST.SConstruction.rawComparisonNext
#print axioms SerrePositivity.KST.SConstruction.rawComparisonNext
#check @SerrePositivity.KST.SConstruction.rawComparisonStage
#print axioms SerrePositivity.KST.SConstruction.rawComparisonStage
#check @SerrePositivity.KST.SConstruction.rawComparisonStage_condition
#print axioms SerrePositivity.KST.SConstruction.rawComparisonStage_condition
#check @SerrePositivity.KST.SConstruction.rawStageFamily_condition
#print axioms SerrePositivity.KST.SConstruction.rawStageFamily_condition
#check @SerrePositivity.KST.SConstruction.rawStageComparisonImage
#print axioms SerrePositivity.KST.SConstruction.rawStageComparisonImage
#check @SerrePositivity.KST.SConstruction.fixedBoundaryHomotopy_restrictions
#print axioms SerrePositivity.KST.SConstruction.fixedBoundaryHomotopy_restrictions
#check @SerrePositivity.KST.SConstruction.sourceFixedBoundaryComposition
#print axioms SerrePositivity.KST.SConstruction.sourceFixedBoundaryComposition
#check @SerrePositivity.KST.SConstruction.FixedBoundaryCompositionData.mk
#print axioms SerrePositivity.KST.SConstruction.FixedBoundaryCompositionData.mk
#check @SerrePositivity.KST.SConstruction.FixedBoundaryCompositionData.homotopy
#print axioms SerrePositivity.KST.SConstruction.FixedBoundaryCompositionData.homotopy
#check @SerrePositivity.KST.SConstruction.FixedBoundaryCompositionData.relative
#print axioms SerrePositivity.KST.SConstruction.FixedBoundaryCompositionData.relative
#check @SerrePositivity.KST.SConstruction.FixedBoundaryCompositionData.triangle
#print axioms SerrePositivity.KST.SConstruction.FixedBoundaryCompositionData.triangle
#check @SerrePositivity.KST.SConstruction.RawComparisonStage.mk
#print axioms SerrePositivity.KST.SConstruction.RawComparisonStage.mk
#check @SerrePositivity.KST.SConstruction.RawComparisonStage.val
#print axioms SerrePositivity.KST.SConstruction.RawComparisonStage.val
#check @SerrePositivity.KST.SConstruction.RawComparisonStage.correction
#print axioms SerrePositivity.KST.SConstruction.RawComparisonStage.correction
#check @SerrePositivity.KST.SConstruction.RawComparisonStage.boundary
#print axioms SerrePositivity.KST.SConstruction.RawComparisonStage.boundary
#check @SerrePositivity.KST.SConstruction.CompositionReplacementTetrahedron.mk
#print axioms SerrePositivity.KST.SConstruction.CompositionReplacementTetrahedron.mk
#check @SerrePositivity.KST.SConstruction.CompositionReplacementTetrahedron.simplex
#print axioms SerrePositivity.KST.SConstruction.CompositionReplacementTetrahedron.simplex
#check @SerrePositivity.KST.SConstruction.CompositionReplacementTetrahedron.original_face
#print axioms SerrePositivity.KST.SConstruction.CompositionReplacementTetrahedron.original_face
#check @SerrePositivity.KST.SConstruction.CompositionReplacementTetrahedron.replacement_face
#print axioms SerrePositivity.KST.SConstruction.CompositionReplacementTetrahedron.replacement_face
#check @SerrePositivity.KST.SConstruction.CompositionReplacementTetrahedron.unit_face
#print axioms SerrePositivity.KST.SConstruction.CompositionReplacementTetrahedron.unit_face
#check @SerrePositivity.KST.SConstruction.CompositionReplacementTetrahedron.triangle
#print axioms SerrePositivity.KST.SConstruction.CompositionReplacementTetrahedron.triangle
#check @SerrePositivity.KST.SConstruction.CompositionReplacementTetrahedron.triangle_face
#print axioms SerrePositivity.KST.SConstruction.CompositionReplacementTetrahedron.triangle_face
#check @SerrePositivity.KST.SConstruction.compositionReplacementTetrahedron
#print axioms SerrePositivity.KST.SConstruction.compositionReplacementTetrahedron
#check @SerrePositivity.KST.SConstruction.enrichedComparisonPinchedEdge
#print axioms SerrePositivity.KST.SConstruction.enrichedComparisonPinchedEdge
#check @SerrePositivity.KST.SConstruction.enrichedComparisonPinchedTriangle
#print axioms SerrePositivity.KST.SConstruction.enrichedComparisonPinchedTriangle
#check @SerrePositivity.KST.SConstruction.enrichedComparisonPinchedTriangle_simplex
#print axioms SerrePositivity.KST.SConstruction.enrichedComparisonPinchedTriangle_simplex
#check @SerrePositivity.KST.SConstruction.enrichedCompositionReplacement
#print axioms SerrePositivity.KST.SConstruction.enrichedCompositionReplacement
#check @SerrePositivity.KST.SConstruction.compositionStringPair_direct
#print axioms SerrePositivity.KST.SConstruction.compositionStringPair_direct
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeDirectBFFamily_boundary
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeDirectBFFamily_boundary
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeBFFamily_boundary
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeCompositeBFFamily_boundary
#check @SerrePositivity.KST.SConstruction.monicKPrismTracedBFCompositionBoundary
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedBFCompositionBoundary
#check @SerrePositivity.KST.SConstruction.monicKPrismTracedBFCompositionBoundary_h
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedBFCompositionBoundary_h
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeBFComparisonData_composition_boundary
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeBFComparisonData_composition_boundary
#check @SerrePositivity.KST.SConstruction.pointFamilyHomotopyEdge
#print axioms SerrePositivity.KST.SConstruction.pointFamilyHomotopyEdge
#check @SerrePositivity.KST.SConstruction.pointFamilyHomotopyEdge_map
#print axioms SerrePositivity.KST.SConstruction.pointFamilyHomotopyEdge_map
#check @SerrePositivity.KST.SConstruction.tracedBoundarySpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedBoundarySpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.monicKTracedSpectrumMap
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSpectrumMap
#check @SerrePositivity.KST.SConstruction.monicKTracedSpectrumMap_vertex
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSpectrumMap_vertex
#check @SerrePositivity.KST.SConstruction.monicKTracedSpectrumMap_comp_vertex
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSpectrumMap_comp_vertex
#check @SerrePositivity.KST.SConstruction.monicKTracedSpectrumCompositionEdge
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSpectrumCompositionEdge
#check @SerrePositivity.KST.SConstruction.monicKTracedSpectrumCompositionEdge_map
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSpectrumCompositionEdge_map
#check @SerrePositivity.KST.SConstruction.tracedCoherentSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedCoherentSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.tracedCoherentSpectrumQuasicategory
#print axioms SerrePositivity.KST.SConstruction.tracedCoherentSpectrumQuasicategory
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentCompositionData
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentCompositionData
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentComposition
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentComposition
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentComposition_face
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentComposition_face
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentComposition_comparison_face
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentComposition_comparison_face
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentComposition_original_face
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentComposition_original_face
#check @SerrePositivity.KST.SConstruction.coherentPathInclusionTriangle
#print axioms SerrePositivity.KST.SConstruction.coherentPathInclusionTriangle
#check @SerrePositivity.KST.SConstruction.coherentDoubleInsertedPath
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleInsertedPath
#check @SerrePositivity.KST.SConstruction.coherentDoubleInsertSecondInclusion
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleInsertSecondInclusion
#check @SerrePositivity.KST.SConstruction.coherentDoubleInsertDiagonal
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleInsertDiagonal
#check @SerrePositivity.KST.SConstruction.coherentDoubleInsertFirstTriangle
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleInsertFirstTriangle
#check @SerrePositivity.KST.SConstruction.coherentDoubleInsertSecondTriangle
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleInsertSecondTriangle
#check @SerrePositivity.KST.SConstruction.coherentDoubleInsertFirstTriangle_simplex
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleInsertFirstTriangle_simplex
#check @SerrePositivity.KST.SConstruction.coherentDoubleInsertSecondTriangle_simplex
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleInsertSecondTriangle_simplex
#check @SerrePositivity.KST.SConstruction.coherentDoubleInsertMappedFirstTriangle
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleInsertMappedFirstTriangle
#check @SerrePositivity.KST.SConstruction.coherentDoubleInsertMappedSecondTriangle
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleInsertMappedSecondTriangle
#check @SerrePositivity.KST.SConstruction.coherentDoubleInsertMappedTriangles_diagonal
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleInsertMappedTriangles_diagonal
#check @SerrePositivity.KST.SConstruction.coherentSimplexFaceMapping_heq
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexFaceMapping_heq
#check @SerrePositivity.KST.SConstruction.compositionTriangleLongEdgeData
#print axioms SerrePositivity.KST.SConstruction.compositionTriangleLongEdgeData
#check @SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.mk
#print axioms SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.mk
#check @SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.simplex
#print axioms SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.simplex
#check @SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.second_face
#print axioms SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.second_face
#check @SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.right_face
#print axioms SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.right_face
#check @SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.first_face
#print axioms SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.first_face
#check @SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.left
#print axioms SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.left
#check @SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.left_face
#print axioms SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.left_face
#check @SerrePositivity.KST.SConstruction.compositionTripleTetrahedron
#print axioms SerrePositivity.KST.SConstruction.compositionTripleTetrahedron
#check @SerrePositivity.KST.SConstruction.tracedTripleSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedTripleSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.tracedTripleSpectrumQuasicategory
#print axioms SerrePositivity.KST.SConstruction.tracedTripleSpectrumQuasicategory
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleData
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleData
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTriplePrescribedLeftData
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTriplePrescribedLeftData
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTriplePrescribedLeft
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTriplePrescribedLeft
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTriplePrescribedLeft_simplex
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTriplePrescribedLeft_simplex
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTriple_first_face
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTriple_first_face
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTriple_second_face
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTriple_second_face
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTriple_right_face
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTriple_right_face
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleGeneratedLeft
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleGeneratedLeft
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleGeneratedLeft_face
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleGeneratedLeft_face
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleGeneratedEdge
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleGeneratedEdge
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTriplePrescribedEdge
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTriplePrescribedEdge
#check @SerrePositivity.KST.SConstruction.tracedTripleFaceSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedTripleFaceSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTriple_first_face_mapping
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTriple_first_face_mapping
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTriple_second_face_mapping
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTriple_second_face_mapping
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTriple_right_face_mapping
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTriple_right_face_mapping
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTriple_generated_face_mapping
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTriple_generated_face_mapping
#check @SerrePositivity.KST.SConstruction.tracedTriplePathSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedTriplePathSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTriplePathMap
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTriplePathMap
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleFirstPathTriangle
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleFirstPathTriangle
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleSecondPathTriangle
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleSecondPathTriangle
#check @SerrePositivity.KST.SConstruction.coherentInsertEndpoint_edge
#print axioms SerrePositivity.KST.SConstruction.coherentInsertEndpoint_edge
#check @SerrePositivity.KST.SConstruction.coherentDoubleInsertFirstUpper_edge
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleInsertFirstUpper_edge
#check @SerrePositivity.KST.SConstruction.coherentDoubleInsertSecondUpper_edge
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleInsertSecondUpper_edge
#check @SerrePositivity.KST.SConstruction.coherentEnrichedPathComposite_app
#print axioms SerrePositivity.KST.SConstruction.coherentEnrichedPathComposite_app
#check @SerrePositivity.KST.SConstruction.coherentDoubleInsertMappedFirstLower
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleInsertMappedFirstLower
#check @SerrePositivity.KST.SConstruction.coherentDoubleInsertMappedSecondLower
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleInsertMappedSecondLower
#check @SerrePositivity.KST.SConstruction.coherentDoubleInsertMappedFirstUpper
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleInsertMappedFirstUpper
#check @SerrePositivity.KST.SConstruction.coherentDoubleInsertMappedSecondUpper
#print axioms SerrePositivity.KST.SConstruction.coherentDoubleInsertMappedSecondUpper
#check @SerrePositivity.KST.SConstruction.coherentEndpointPathComposite_map
#print axioms SerrePositivity.KST.SConstruction.coherentEndpointPathComposite_map
#check @SerrePositivity.KST.SConstruction.coherentEndpointPathToComposite_map_edge
#print axioms SerrePositivity.KST.SConstruction.coherentEndpointPathToComposite_map_edge
#check @SerrePositivity.KST.SConstruction.coherentSimplexCompositionEdge_naturality
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexCompositionEdge_naturality
#check @SerrePositivity.KST.SConstruction.coherentTriangleCompositionEdge_heq
#print axioms SerrePositivity.KST.SConstruction.coherentTriangleCompositionEdge_heq
#check @SerrePositivity.KST.SConstruction.coherentSimplexCompositionEdge_heq
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexCompositionEdge_heq
#check @SerrePositivity.KST.SConstruction.coherentSimplexArrow_specified_heq
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexArrow_specified_heq
#check @SerrePositivity.KST.SConstruction.coherentTetrahedronFaceComparison_heq
#print axioms SerrePositivity.KST.SConstruction.coherentTetrahedronFaceComparison_heq
#check @SerrePositivity.KST.SConstruction.coherentSimplexEndpointIdentity_edge
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexEndpointIdentity_edge
#check @SerrePositivity.KST.SConstruction.coherentSimplexFirstInsertionTriangle
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexFirstInsertionTriangle
#check @SerrePositivity.KST.SConstruction.coherentSimplexSecondInsertionTriangle
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexSecondInsertionTriangle
#check @SerrePositivity.KST.SConstruction.coherentSimplexFirstInsertion_lower
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexFirstInsertion_lower
#check @SerrePositivity.KST.SConstruction.coherentSimplexSecondInsertion_lower
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexSecondInsertion_lower
#check @SerrePositivity.KST.SConstruction.coherentSimplexFirstInsertion_upper
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexFirstInsertion_upper
#check @SerrePositivity.KST.SConstruction.coherentSimplexSecondInsertion_upper
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexSecondInsertion_upper
#check @SerrePositivity.KST.SConstruction.coherentTetrahedron_vertices
#print axioms SerrePositivity.KST.SConstruction.coherentTetrahedron_vertices
#check @SerrePositivity.KST.SConstruction.coherentTetrahedronFirstUpper_heq
#print axioms SerrePositivity.KST.SConstruction.coherentTetrahedronFirstUpper_heq
#check @SerrePositivity.KST.SConstruction.coherentTetrahedronSecondUpper_heq
#print axioms SerrePositivity.KST.SConstruction.coherentTetrahedronSecondUpper_heq
#check @SerrePositivity.KST.SConstruction.tracedTripleComparisonSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedTripleComparisonSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleFirstLower_heq
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleFirstLower_heq
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleSecondLower_heq
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleSecondLower_heq
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleFirstUpper_heq
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleFirstUpper_heq
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleSecondUpper_heq
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleSecondUpper_heq
#check @SerrePositivity.KST.SConstruction.simplicialEqualityTransport_app_heq
#print axioms SerrePositivity.KST.SConstruction.simplicialEqualityTransport_app_heq
#check @SerrePositivity.KST.SConstruction.simplicialEqualityTransport_app_of_heq
#print axioms SerrePositivity.KST.SConstruction.simplicialEqualityTransport_app_of_heq
#check @SerrePositivity.KST.SConstruction.simplicialEqualityTransport_face
#print axioms SerrePositivity.KST.SConstruction.simplicialEqualityTransport_face
#check @SerrePositivity.KST.SConstruction.simplicialEqualityTransport_face_of_heq
#print axioms SerrePositivity.KST.SConstruction.simplicialEqualityTransport_face_of_heq
#check @SerrePositivity.KST.SConstruction.simplicialEqualityTransport_common_face
#print axioms SerrePositivity.KST.SConstruction.simplicialEqualityTransport_common_face
#check @SerrePositivity.KST.SConstruction.TriangleDiamondData.mk
#print axioms SerrePositivity.KST.SConstruction.TriangleDiamondData.mk
#check @SerrePositivity.KST.SConstruction.TriangleDiamondData.first
#print axioms SerrePositivity.KST.SConstruction.TriangleDiamondData.first
#check @SerrePositivity.KST.SConstruction.TriangleDiamondData.second
#print axioms SerrePositivity.KST.SConstruction.TriangleDiamondData.second
#check @SerrePositivity.KST.SConstruction.TriangleDiamondData.first_lower
#print axioms SerrePositivity.KST.SConstruction.TriangleDiamondData.first_lower
#check @SerrePositivity.KST.SConstruction.TriangleDiamondData.second_lower
#print axioms SerrePositivity.KST.SConstruction.TriangleDiamondData.second_lower
#check @SerrePositivity.KST.SConstruction.TriangleDiamondData.first_upper
#print axioms SerrePositivity.KST.SConstruction.TriangleDiamondData.first_upper
#check @SerrePositivity.KST.SConstruction.TriangleDiamondData.second_upper
#print axioms SerrePositivity.KST.SConstruction.TriangleDiamondData.second_upper
#check @SerrePositivity.KST.SConstruction.TriangleDiamondData.diagonal
#print axioms SerrePositivity.KST.SConstruction.TriangleDiamondData.diagonal
#check @SerrePositivity.KST.SConstruction.triangleDiamondTransportData
#print axioms SerrePositivity.KST.SConstruction.triangleDiamondTransportData
#check @SerrePositivity.KST.SConstruction.tracedTripleMappingSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedTripleMappingSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleMappingSpace_eq
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleMappingSpace_eq
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTriplePathTriangles_diagonal
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTriplePathTriangles_diagonal
#check @SerrePositivity.KST.SConstruction.tracedTripleDiamondSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedTripleDiamondSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleDiamondData
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleDiamondData
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleDiamond
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleDiamond
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleDiamond_first_image
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleDiamond_first_image
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleDiamond_second_image
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleDiamond_second_image
#check @SerrePositivity.KST.SConstruction.CompositionDiamond.mk
#print axioms SerrePositivity.KST.SConstruction.CompositionDiamond.mk
#check @SerrePositivity.KST.SConstruction.CompositionDiamond.diagonal
#print axioms SerrePositivity.KST.SConstruction.CompositionDiamond.diagonal
#check @SerrePositivity.KST.SConstruction.CompositionDiamond.first
#print axioms SerrePositivity.KST.SConstruction.CompositionDiamond.first
#check @SerrePositivity.KST.SConstruction.CompositionDiamond.second
#print axioms SerrePositivity.KST.SConstruction.CompositionDiamond.second
#check @SerrePositivity.KST.SConstruction.triangleDiamondCompositionData
#print axioms SerrePositivity.KST.SConstruction.triangleDiamondCompositionData
#check @SerrePositivity.KST.SConstruction.TriangleDiamondData.ofEq
#print axioms SerrePositivity.KST.SConstruction.TriangleDiamondData.ofEq
#check @SerrePositivity.KST.SConstruction.enrichedComparisonLeftWhisker
#print axioms SerrePositivity.KST.SConstruction.enrichedComparisonLeftWhisker
#check @SerrePositivity.KST.SConstruction.enrichedComparisonLeftWhisker_edge
#print axioms SerrePositivity.KST.SConstruction.enrichedComparisonLeftWhisker_edge
#check @SerrePositivity.KST.SConstruction.enrichedComparisonRightWhisker
#print axioms SerrePositivity.KST.SConstruction.enrichedComparisonRightWhisker
#check @SerrePositivity.KST.SConstruction.enrichedComparisonRightWhisker_edge
#print axioms SerrePositivity.KST.SConstruction.enrichedComparisonRightWhisker_edge
#check @SerrePositivity.KST.SConstruction.tracedTripleWhiskerSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedTripleWhiskerSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleFirstWhisker
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleFirstWhisker
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleSecondWhisker
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleSecondWhisker
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleEdgeDiamond
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleEdgeDiamond
#check @SerrePositivity.KST.SConstruction.tracedTripleCompositionSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedTripleCompositionSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleCompositionDiamondData
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleCompositionDiamondData
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleCompositionDiamond
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleCompositionDiamond
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleCompositionDiamond_first_image
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleCompositionDiamond_first_image
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleCompositionDiamond_second_image
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleCompositionDiamond_second_image
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleCompositionDiamond_diagonal
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleCompositionDiamond_diagonal
#check @SerrePositivity.KST.SConstruction.pinchedComparisonEndpoint_maximum
#print axioms SerrePositivity.KST.SConstruction.pinchedComparisonEndpoint_maximum
#check @SerrePositivity.KST.SConstruction.pinchedComparisonComposite_maximum
#print axioms SerrePositivity.KST.SConstruction.pinchedComparisonComposite_maximum
#check @SerrePositivity.KST.SConstruction.pinchedComparisonCoordinate_edge
#print axioms SerrePositivity.KST.SConstruction.pinchedComparisonCoordinate_edge
#check @SerrePositivity.KST.SConstruction.coherentHomComparisonSimplex_edge_heq
#print axioms SerrePositivity.KST.SConstruction.coherentHomComparisonSimplex_edge_heq
#check @SerrePositivity.KST.SConstruction.enrichedComparisonPinchedTriangle_original
#print axioms SerrePositivity.KST.SConstruction.enrichedComparisonPinchedTriangle_original
#check @SerrePositivity.KST.SConstruction.enrichedComparisonPinchedTriangle_decoded_heq
#print axioms SerrePositivity.KST.SConstruction.enrichedComparisonPinchedTriangle_decoded_heq
#check @SerrePositivity.KST.SConstruction.coherentEndpointPathLeftUnit_edge
#print axioms SerrePositivity.KST.SConstruction.coherentEndpointPathLeftUnit_edge
#check @SerrePositivity.KST.SConstruction.coherentSimplexCompositionEdge_leftUnit
#print axioms SerrePositivity.KST.SConstruction.coherentSimplexCompositionEdge_leftUnit
#check @SerrePositivity.KST.SConstruction.coherentNerveCompStruct_comparison_edge_heq
#print axioms SerrePositivity.KST.SConstruction.coherentNerveCompStruct_comparison_edge_heq
#check @SerrePositivity.KST.SConstruction.coherentNerveIdComp_comparison_edge_heq
#print axioms SerrePositivity.KST.SConstruction.coherentNerveIdComp_comparison_edge_heq
#check @SerrePositivity.KST.SConstruction.coherentNerveUnitCompStruct
#print axioms SerrePositivity.KST.SConstruction.coherentNerveUnitCompStruct
#check @SerrePositivity.KST.SConstruction.coherentNerveUnitCompStruct_simplex
#print axioms SerrePositivity.KST.SConstruction.coherentNerveUnitCompStruct_simplex
#check @SerrePositivity.KST.SConstruction.coherentNerveCompStruct_decoded_edge
#print axioms SerrePositivity.KST.SConstruction.coherentNerveCompStruct_decoded_edge
#check @SerrePositivity.KST.SConstruction.coherentNerveUnitCompStruct_decoded_edge
#print axioms SerrePositivity.KST.SConstruction.coherentNerveUnitCompStruct_decoded_edge
#check @SerrePositivity.KST.SConstruction.simplicialHom_identityEdges_comp
#print axioms SerrePositivity.KST.SConstruction.simplicialHom_identityEdges_comp
#check @SerrePositivity.KST.SConstruction.enrichedReplacementFirstLower_heq
#print axioms SerrePositivity.KST.SConstruction.enrichedReplacementFirstLower_heq
#check @SerrePositivity.KST.SConstruction.enrichedReplacementSecondLower_heq
#print axioms SerrePositivity.KST.SConstruction.enrichedReplacementSecondLower_heq
#check @SerrePositivity.KST.SConstruction.enrichedReplacementFirstUpper_heq
#print axioms SerrePositivity.KST.SConstruction.enrichedReplacementFirstUpper_heq
#check @SerrePositivity.KST.SConstruction.enrichedReplacementSecondUpper_heq
#print axioms SerrePositivity.KST.SConstruction.enrichedReplacementSecondUpper_heq
#check @SerrePositivity.KST.SConstruction.enrichedReplacementMappingSpace_eq
#print axioms SerrePositivity.KST.SConstruction.enrichedReplacementMappingSpace_eq
#check @SerrePositivity.KST.SConstruction.enrichedReplacementPathTriangles_diagonal
#print axioms SerrePositivity.KST.SConstruction.enrichedReplacementPathTriangles_diagonal
#check @SerrePositivity.KST.SConstruction.enrichedReplacementRawDiamondData
#print axioms SerrePositivity.KST.SConstruction.enrichedReplacementRawDiamondData
#check @SerrePositivity.KST.SConstruction.enrichedReplacementComparisonData
#print axioms SerrePositivity.KST.SConstruction.enrichedReplacementComparisonData
#check @SerrePositivity.KST.SConstruction.enrichedReplacementComparison
#print axioms SerrePositivity.KST.SConstruction.enrichedReplacementComparison
#check @SerrePositivity.KST.SConstruction.enrichedReplacementComparison_first_image
#print axioms SerrePositivity.KST.SConstruction.enrichedReplacementComparison_first_image
#check @SerrePositivity.KST.SConstruction.enrichedReplacementComparison_second_image
#print axioms SerrePositivity.KST.SConstruction.enrichedReplacementComparison_second_image
#check @SerrePositivity.KST.SConstruction.tracedCompositionRecoverySpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedCompositionRecoverySpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryData
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryData
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionRecovery
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionRecovery
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionRecovery_first_image
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionRecovery_first_image
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionRecovery_second_image
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionRecovery_second_image
#check @SerrePositivity.KST.SConstruction.FixedBoundaryCospanData.mk
#print axioms SerrePositivity.KST.SConstruction.FixedBoundaryCospanData.mk
#check @SerrePositivity.KST.SConstruction.FixedBoundaryCospanData.homotopy
#print axioms SerrePositivity.KST.SConstruction.FixedBoundaryCospanData.homotopy
#check @SerrePositivity.KST.SConstruction.FixedBoundaryCospanData.relative
#print axioms SerrePositivity.KST.SConstruction.FixedBoundaryCospanData.relative
#check @SerrePositivity.KST.SConstruction.FixedBoundaryCospanData.triangle
#print axioms SerrePositivity.KST.SConstruction.FixedBoundaryCospanData.triangle
#check @SerrePositivity.KST.SConstruction.fixedBoundaryCospanData
#print axioms SerrePositivity.KST.SConstruction.fixedBoundaryCospanData
#check @SerrePositivity.KST.SConstruction.parallelEdge_boundary_eq
#print axioms SerrePositivity.KST.SConstruction.parallelEdge_boundary_eq
#check @SerrePositivity.KST.SConstruction.endpointFixedTriangleHomotopy
#print axioms SerrePositivity.KST.SConstruction.endpointFixedTriangleHomotopy
#check @SerrePositivity.KST.SConstruction.endpointFixedTriangleHomotopy_relative
#print axioms SerrePositivity.KST.SConstruction.endpointFixedTriangleHomotopy_relative
#check @SerrePositivity.KST.SConstruction.endpointFixedTriangleHomotopy_triangle
#print axioms SerrePositivity.KST.SConstruction.endpointFixedTriangleHomotopy_triangle
#check @SerrePositivity.KST.SConstruction.endpointFixedDiamondComparisonData
#print axioms SerrePositivity.KST.SConstruction.endpointFixedDiamondComparisonData
#check @SerrePositivity.KST.SConstruction.endpointFixedDiamondComparison
#print axioms SerrePositivity.KST.SConstruction.endpointFixedDiamondComparison
#check @SerrePositivity.KST.SConstruction.endpointFixedDiamondComparison_relative
#print axioms SerrePositivity.KST.SConstruction.endpointFixedDiamondComparison_relative
#check @SerrePositivity.KST.SConstruction.endpointFixedDiamondComparisonRealization
#print axioms SerrePositivity.KST.SConstruction.endpointFixedDiamondComparisonRealization
#check @SerrePositivity.KST.SConstruction.endpointFixedDiamondComparisonRealization_comparison
#print axioms SerrePositivity.KST.SConstruction.endpointFixedDiamondComparisonRealization_comparison
#check @SerrePositivity.KST.SConstruction.endpointFixedDiamondComparisonRealization_first
#print axioms SerrePositivity.KST.SConstruction.endpointFixedDiamondComparisonRealization_first
#check @SerrePositivity.KST.SConstruction.endpointFixedDiamondComparisonRealization_second
#print axioms SerrePositivity.KST.SConstruction.endpointFixedDiamondComparisonRealization_second
#check @SerrePositivity.KST.SConstruction.endpointFixedDiamondComparisonRealization_first_triangle
#print axioms SerrePositivity.KST.SConstruction.endpointFixedDiamondComparisonRealization_first_triangle
#check @SerrePositivity.KST.SConstruction.endpointFixedDiamondComparisonRealization_second_triangle
#print axioms SerrePositivity.KST.SConstruction.endpointFixedDiamondComparisonRealization_second_triangle
#check @SerrePositivity.KST.SConstruction.tracedRecoveryCylinderSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedRecoveryCylinderSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.tracedRecoveryCylinderMappingKan
#print axioms SerrePositivity.KST.SConstruction.tracedRecoveryCylinderMappingKan
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinderData
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinderData
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinder
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinder
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinder_relative
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinder_relative
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinderRealization
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinderRealization
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinderRealization_comparison
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinderRealization_comparison
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinderRealization_first
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinderRealization_first
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinderRealization_second
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinderRealization_second
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinderRealization_first_triangle
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinderRealization_first_triangle
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinderRealization_second_triangle
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinderRealization_second_triangle
#check @SerrePositivity.KST.SConstruction.FixedBoundaryCospanData.triangle_relative
#print axioms SerrePositivity.KST.SConstruction.FixedBoundaryCospanData.triangle_relative
#check @SerrePositivity.KST.SConstruction.endpointFixedDiamondComparisonRealization_relative
#print axioms SerrePositivity.KST.SConstruction.endpointFixedDiamondComparisonRealization_relative
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinderRealization_relative
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionRecoveryCylinderRealization_relative
#check @SerrePositivity.KST.SConstruction.enrichedFixedLeftComposition
#print axioms SerrePositivity.KST.SConstruction.enrichedFixedLeftComposition
#check @SerrePositivity.KST.SConstruction.enrichedFixedRightComposition
#print axioms SerrePositivity.KST.SConstruction.enrichedFixedRightComposition
#check @SerrePositivity.KST.SConstruction.enrichedComparisonLeftWhisker_map
#print axioms SerrePositivity.KST.SConstruction.enrichedComparisonLeftWhisker_map
#check @SerrePositivity.KST.SConstruction.enrichedComparisonRightWhisker_map
#print axioms SerrePositivity.KST.SConstruction.enrichedComparisonRightWhisker_map
#check @SerrePositivity.KST.SConstruction.fixedBoundaryHomotopy_postcomp
#print axioms SerrePositivity.KST.SConstruction.fixedBoundaryHomotopy_postcomp
#check @SerrePositivity.KST.SConstruction.fixedBoundaryFamily_postcomp
#print axioms SerrePositivity.KST.SConstruction.fixedBoundaryFamily_postcomp
#check @SerrePositivity.KST.SConstruction.enrichedLeftWhiskerHomotopy
#print axioms SerrePositivity.KST.SConstruction.enrichedLeftWhiskerHomotopy
#check @SerrePositivity.KST.SConstruction.enrichedLeftWhiskerHomotopy_h
#print axioms SerrePositivity.KST.SConstruction.enrichedLeftWhiskerHomotopy_h
#check @SerrePositivity.KST.SConstruction.enrichedLeftWhiskerHomotopy_relative
#print axioms SerrePositivity.KST.SConstruction.enrichedLeftWhiskerHomotopy_relative
#check @SerrePositivity.KST.SConstruction.enrichedRightWhiskerHomotopy
#print axioms SerrePositivity.KST.SConstruction.enrichedRightWhiskerHomotopy
#check @SerrePositivity.KST.SConstruction.enrichedRightWhiskerHomotopy_h
#print axioms SerrePositivity.KST.SConstruction.enrichedRightWhiskerHomotopy_h
#check @SerrePositivity.KST.SConstruction.enrichedRightWhiskerHomotopy_relative
#print axioms SerrePositivity.KST.SConstruction.enrichedRightWhiskerHomotopy_relative
#check @SerrePositivity.KST.SConstruction.tracedFirstWhiskerRecoverySpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedFirstWhiskerRecoverySpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeFirstWhisker
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeFirstWhisker
#check @SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecovery
#print axioms SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecovery
#check @SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecovery_relative
#print axioms SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecovery_relative
#check @SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecoveryRealization
#print axioms SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecoveryRealization
#check @SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecoveryRealization_relative
#print axioms SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecoveryRealization_relative
#check @SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecoveryRealization_comparison
#print axioms SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecoveryRealization_comparison
#check @SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecoveryRealization_first
#print axioms SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecoveryRealization_first
#check @SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecoveryRealization_first_triangle
#print axioms SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecoveryRealization_first_triangle
#check @SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecoveryRealization_second
#print axioms SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecoveryRealization_second
#check @SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecoveryRealization_second_triangle
#print axioms SerrePositivity.KST.SConstruction.monicKTracedFirstWhiskerRecoveryRealization_second_triangle
#check @SerrePositivity.KST.SConstruction.tracedSecondWhiskerRecoverySpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedSecondWhiskerRecoverySpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeSecondWhisker
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeSecondWhisker
#check @SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecovery
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecovery
#check @SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecovery_relative
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecovery_relative
#check @SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecoveryRealization
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecoveryRealization
#check @SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecoveryRealization_relative
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecoveryRealization_relative
#check @SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecoveryRealization_comparison
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecoveryRealization_comparison
#check @SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecoveryRealization_first
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecoveryRealization_first
#check @SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecoveryRealization_first_triangle
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecoveryRealization_first_triangle
#check @SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecoveryRealization_second
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecoveryRealization_second
#check @SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecoveryRealization_second_triangle
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSecondWhiskerRecoveryRealization_second_triangle
#check @SerrePositivity.KST.SConstruction.FaceTransportFromOneData.mk
#print axioms SerrePositivity.KST.SConstruction.FaceTransportFromOneData.mk
#check @SerrePositivity.KST.SConstruction.FaceTransportFromOneData.val
#print axioms SerrePositivity.KST.SConstruction.FaceTransportFromOneData.val
#check @SerrePositivity.KST.SConstruction.FaceTransportFromOneData.restriction
#print axioms SerrePositivity.KST.SConstruction.FaceTransportFromOneData.restriction
#check @SerrePositivity.KST.SConstruction.FaceTransportFromOneData.comparison
#print axioms SerrePositivity.KST.SConstruction.FaceTransportFromOneData.comparison
#check @SerrePositivity.KST.SConstruction.FaceTransportFromOneData.comparison_boundary
#print axioms SerrePositivity.KST.SConstruction.FaceTransportFromOneData.comparison_boundary
#check @SerrePositivity.KST.SConstruction.faceTransportFromOneData
#print axioms SerrePositivity.KST.SConstruction.faceTransportFromOneData
#check @SerrePositivity.KST.SConstruction.triangleTransportFromOneData
#print axioms SerrePositivity.KST.SConstruction.triangleTransportFromOneData
#check @SerrePositivity.KST.SConstruction.triangleTransportFromOne
#print axioms SerrePositivity.KST.SConstruction.triangleTransportFromOne
#check @SerrePositivity.KST.SConstruction.triangleTransportFromOne_face
#print axioms SerrePositivity.KST.SConstruction.triangleTransportFromOne_face
#check @SerrePositivity.KST.SConstruction.triangleTransportFromOneComparison
#print axioms SerrePositivity.KST.SConstruction.triangleTransportFromOneComparison
#check @SerrePositivity.KST.SConstruction.triangleTransportFromOneComparison_h
#print axioms SerrePositivity.KST.SConstruction.triangleTransportFromOneComparison_h
#check @SerrePositivity.KST.SConstruction.triangleTransportFromOneComparison_boundary
#print axioms SerrePositivity.KST.SConstruction.triangleTransportFromOneComparison_boundary
#check @SerrePositivity.KST.SConstruction.triangleTransportFromOneComparison_fixed_face
#print axioms SerrePositivity.KST.SConstruction.triangleTransportFromOneComparison_fixed_face
#check @SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinder.mk
#print axioms SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinder.mk
#check @SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinder.homotopy
#print axioms SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinder.homotopy
#check @SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinder.relative
#print axioms SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinder.relative
#check @SerrePositivity.KST.SConstruction.endpointFixedEdgeCylinderRefl
#print axioms SerrePositivity.KST.SConstruction.endpointFixedEdgeCylinderRefl
#check @SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinder.vertex
#print axioms SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinder.vertex
#check @SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinder.curry
#print axioms SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinder.curry
#check @SerrePositivity.KST.SConstruction.endpointFixedEdgeCylinder_curry_vertex_eq
#print axioms SerrePositivity.KST.SConstruction.endpointFixedEdgeCylinder_curry_vertex_eq
#check @SerrePositivity.KST.SConstruction.triangleBoundaryCylinderFaces
#print axioms SerrePositivity.KST.SConstruction.triangleBoundaryCylinderFaces
#check @SerrePositivity.KST.SConstruction.triangleBoundaryCylinderFaces_compatible
#print axioms SerrePositivity.KST.SConstruction.triangleBoundaryCylinderFaces_compatible
#check @SerrePositivity.KST.SConstruction.triangleBoundaryCylinderMap
#print axioms SerrePositivity.KST.SConstruction.triangleBoundaryCylinderMap
#check @SerrePositivity.KST.SConstruction.triangleBoundaryCylinderRawFaces
#print axioms SerrePositivity.KST.SConstruction.triangleBoundaryCylinderRawFaces
#check @SerrePositivity.KST.SConstruction.triangleBoundaryCylinderMap_face
#print axioms SerrePositivity.KST.SConstruction.triangleBoundaryCylinderMap_face
#check @SerrePositivity.KST.SConstruction.triangleBoundaryHomotopy
#print axioms SerrePositivity.KST.SConstruction.triangleBoundaryHomotopy
#check @SerrePositivity.KST.SConstruction.triangleBoundaryHomotopy_face
#print axioms SerrePositivity.KST.SConstruction.triangleBoundaryHomotopy_face
#check @SerrePositivity.KST.SConstruction.triangleBoundaryMap_of_compStruct
#print axioms SerrePositivity.KST.SConstruction.triangleBoundaryMap_of_compStruct
#check @SerrePositivity.KST.SConstruction.triangleEdgeTransportBoundary
#print axioms SerrePositivity.KST.SConstruction.triangleEdgeTransportBoundary
#check @SerrePositivity.KST.SConstruction.triangleEdgeTransport
#print axioms SerrePositivity.KST.SConstruction.triangleEdgeTransport
#check @SerrePositivity.KST.SConstruction.triangleEdgeTransportComparison
#print axioms SerrePositivity.KST.SConstruction.triangleEdgeTransportComparison
#check @SerrePositivity.KST.SConstruction.triangleEdgeTransportComparison_boundary
#print axioms SerrePositivity.KST.SConstruction.triangleEdgeTransportComparison_boundary
#check @SerrePositivity.KST.SConstruction.triangleEdgeTransportComparison_face
#print axioms SerrePositivity.KST.SConstruction.triangleEdgeTransportComparison_face
#check @SerrePositivity.KST.SConstruction.triangleEdgeTransportComparison_fixed_diagonal
#print axioms SerrePositivity.KST.SConstruction.triangleEdgeTransportComparison_fixed_diagonal
#check @SerrePositivity.KST.SConstruction.compositionDiamondEdgeTransport
#print axioms SerrePositivity.KST.SConstruction.compositionDiamondEdgeTransport
#check @SerrePositivity.KST.SConstruction.compositionDiamondEdgeTransportFirstComparison
#print axioms SerrePositivity.KST.SConstruction.compositionDiamondEdgeTransportFirstComparison
#check @SerrePositivity.KST.SConstruction.compositionDiamondEdgeTransportSecondComparison
#print axioms SerrePositivity.KST.SConstruction.compositionDiamondEdgeTransportSecondComparison
#check @SerrePositivity.KST.SConstruction.compositionDiamondEdgeTransportFirstComparison_diagonal
#print axioms SerrePositivity.KST.SConstruction.compositionDiamondEdgeTransportFirstComparison_diagonal
#check @SerrePositivity.KST.SConstruction.compositionDiamondEdgeTransportSecondComparison_diagonal
#print axioms SerrePositivity.KST.SConstruction.compositionDiamondEdgeTransportSecondComparison_diagonal
#check @SerrePositivity.KST.SConstruction.compositionDiamondEdgeTransportFirstComparison_face
#print axioms SerrePositivity.KST.SConstruction.compositionDiamondEdgeTransportFirstComparison_face
#check @SerrePositivity.KST.SConstruction.compositionDiamondEdgeTransportSecondComparison_face
#print axioms SerrePositivity.KST.SConstruction.compositionDiamondEdgeTransportSecondComparison_face
#check @SerrePositivity.KST.SConstruction.tracedTripleEdgeTransportSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedTripleEdgeTransportSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.tracedTripleEdgeTransportMappingKan
#print axioms SerrePositivity.KST.SConstruction.tracedTripleEdgeTransportMappingKan
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleLowerRecoveryCylinder
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleLowerRecoveryCylinder
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleFirstRecoveryCylinder
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleFirstRecoveryCylinder
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleSecondRecoveryCylinder
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleSecondRecoveryCylinder
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeTripleCompositionDiamond
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeTripleCompositionDiamond
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeTripleFirstComparison
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeTripleFirstComparison
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeTripleSecondComparison
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeTripleSecondComparison
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeTripleCompositionDiamond_diagonal
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeTripleCompositionDiamond_diagonal
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeTripleFirstComparison_diagonal
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeTripleFirstComparison_diagonal
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeTripleSecondComparison_diagonal
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeTripleSecondComparison_diagonal
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeTripleFirstComparison_lower
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeTripleFirstComparison_lower
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeTripleFirstComparison_upper
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeTripleFirstComparison_upper
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeTripleSecondComparison_upper
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeTripleSecondComparison_upper
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeTripleSecondComparison_lower
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeTripleSecondComparison_lower
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeTripleFirstComparison_original
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeTripleFirstComparison_original
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeTripleSecondComparison_original
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeTripleSecondComparison_original
#check @SerrePositivity.KST.SConstruction.edgeSourceTransportData
#print axioms SerrePositivity.KST.SConstruction.edgeSourceTransportData
#check @SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinder.postcomp
#print axioms SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinder.postcomp
#check @SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinder.postcomp_h
#print axioms SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinder.postcomp_h
#check @SerrePositivity.KST.SConstruction.endpointFixedCylinderLiftData
#print axioms SerrePositivity.KST.SConstruction.endpointFixedCylinderLiftData
#check @SerrePositivity.KST.SConstruction.endpointFixedCylinder_nonempty_iff
#print axioms SerrePositivity.KST.SConstruction.endpointFixedCylinder_nonempty_iff
#check @SerrePositivity.KST.SConstruction.tracedTripleRawBoundarySpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedTripleRawBoundarySpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeTriplePrescribedEdgeData
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeTriplePrescribedEdgeData
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeTriplePrescribedEdge
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeTriplePrescribedEdge
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeTriplePrescribedEdge_edge
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeTriplePrescribedEdge_edge
#check @SerrePositivity.KST.SConstruction.MonicKTracedTripleRawComparison
#print axioms SerrePositivity.KST.SConstruction.MonicKTracedTripleRawComparison
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleRawComparison_nonempty_iff
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleRawComparison_nonempty_iff
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleFourthEdgeLiftData
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleFourthEdgeLiftData
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleFourthEdgeLiftData_projection
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleFourthEdgeLiftData_projection
#check @SerrePositivity.KST.SConstruction.tracedTripleRawFacesSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedTripleRawFacesSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.monicKPrismTracedBFCompositionBoundary_projection
#print axioms SerrePositivity.KST.SConstruction.monicKPrismTracedBFCompositionBoundary_projection
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeTriplePrescribedEdge_raw
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeTriplePrescribedEdge_raw
#check @SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleGeneratedEdge_raw
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCoherentTripleGeneratedEdge_raw
#check @SerrePositivity.KST.SConstruction.compositionDiamondFourthEdgeTransportData
#print axioms SerrePositivity.KST.SConstruction.compositionDiamondFourthEdgeTransportData
#check @SerrePositivity.KST.SConstruction.compositionDiamondFourthEdgeTransport
#print axioms SerrePositivity.KST.SConstruction.compositionDiamondFourthEdgeTransport
#check @SerrePositivity.KST.SConstruction.compositionDiamondFourthEdgeTransport_first
#print axioms SerrePositivity.KST.SConstruction.compositionDiamondFourthEdgeTransport_first
#check @SerrePositivity.KST.SConstruction.compositionDiamondFourthEdgeTransport_diagonal
#print axioms SerrePositivity.KST.SConstruction.compositionDiamondFourthEdgeTransport_diagonal
#check @SerrePositivity.KST.SConstruction.compositionDiamondFourthEdgeTransportComparison
#print axioms SerrePositivity.KST.SConstruction.compositionDiamondFourthEdgeTransportComparison
#check @SerrePositivity.KST.SConstruction.compositionDiamondFourthEdgeTransportComparison_face
#print axioms SerrePositivity.KST.SConstruction.compositionDiamondFourthEdgeTransportComparison_face
#check @SerrePositivity.KST.SConstruction.tracedFourthEdgeSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedFourthEdgeSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.tracedFourthEdgeMappingKan
#print axioms SerrePositivity.KST.SConstruction.tracedFourthEdgeMappingKan
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleCompositionDiamondFromRaw
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleCompositionDiamondFromRaw
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleFourthTriangleFromRaw
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleFourthTriangleFromRaw
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleCompositionDiamondFromRaw_first
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleCompositionDiamondFromRaw_first
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleCompositionDiamondFromRaw_diagonal
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleCompositionDiamondFromRaw_diagonal
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleFourthTriangleComparison
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleFourthTriangleComparison
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleFourthTriangleComparison_lower_projection
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleFourthTriangleComparison_lower_projection
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleFourthTriangleComparison_upper
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleFourthTriangleComparison_upper
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleFourthTriangleComparison_diagonal
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleFourthTriangleComparison_diagonal
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleFourthTriangleOriginalChain
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleFourthTriangleOriginalChain
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleFourthTriangleOriginalChain_trace
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleFourthTriangleOriginalChain_trace
#check @SerrePositivity.KST.SConstruction.tracedCompositionZeroSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedCompositionZeroSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.kRawMappingProjection_zero
#print axioms SerrePositivity.KST.SConstruction.kRawMappingProjection_zero
#check @SerrePositivity.KST.SConstruction.monicKTracedSpectrumCompositionEdge_raw_zero
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSpectrumCompositionEdge_raw_zero
#check @SerrePositivity.KST.SConstruction.monicKTracedSpectrumCompositionEdge_zero
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSpectrumCompositionEdge_zero
#check @SerrePositivity.KST.SConstruction.fixedFactorEvaluationPointedSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.fixedFactorEvaluationPointedSimplicialCategory
#check @SerrePositivity.KST.SConstruction.fixedFactorEvaluationSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.fixedFactorEvaluationSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.spectrumFixedLeftComposition_evaluation
#print axioms SerrePositivity.KST.SConstruction.spectrumFixedLeftComposition_evaluation
#check @SerrePositivity.KST.SConstruction.spectrumFixedRightComposition_evaluation
#print axioms SerrePositivity.KST.SConstruction.spectrumFixedRightComposition_evaluation
#check @SerrePositivity.KST.SConstruction.constantEdge_map
#print axioms SerrePositivity.KST.SConstruction.constantEdge_map
#check @SerrePositivity.KST.SConstruction.constantEdge_endpoints
#print axioms SerrePositivity.KST.SConstruction.constantEdge_endpoints
#check @SerrePositivity.KST.SConstruction.constantEdge_source
#print axioms SerrePositivity.KST.SConstruction.constantEdge_source
#check @SerrePositivity.KST.SConstruction.constantEdge_target
#print axioms SerrePositivity.KST.SConstruction.constantEdge_target
#check @SerrePositivity.KST.SConstruction.constantDiamondAtSourceData
#print axioms SerrePositivity.KST.SConstruction.constantDiamondAtSourceData
#check @SerrePositivity.KST.SConstruction.constantDiamondEdgeComparison
#print axioms SerrePositivity.KST.SConstruction.constantDiamondEdgeComparison
#check @SerrePositivity.KST.SConstruction.constantDiamondEdgeComparisonRealization
#print axioms SerrePositivity.KST.SConstruction.constantDiamondEdgeComparisonRealization
#check @SerrePositivity.KST.SConstruction.constantDiamondEdgeComparisonRealization_comparison
#print axioms SerrePositivity.KST.SConstruction.constantDiamondEdgeComparisonRealization_comparison
#check @SerrePositivity.KST.SConstruction.constantDiamondEdgeComparisonRealization_first_triangle
#print axioms SerrePositivity.KST.SConstruction.constantDiamondEdgeComparisonRealization_first_triangle
#check @SerrePositivity.KST.SConstruction.constantDiamondEdgeComparisonRealization_second_triangle
#print axioms SerrePositivity.KST.SConstruction.constantDiamondEdgeComparisonRealization_second_triangle
#check @SerrePositivity.KST.SConstruction.constantDiamondEdgeComparisonRealization_relative
#print axioms SerrePositivity.KST.SConstruction.constantDiamondEdgeComparisonRealization_relative
#check @SerrePositivity.KST.SConstruction.whiskerEvaluationPointedSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.whiskerEvaluationPointedSimplicialCategory
#check @SerrePositivity.KST.SConstruction.whiskerEvaluationSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.whiskerEvaluationSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.spectrumComparisonLeftWhisker_constant
#print axioms SerrePositivity.KST.SConstruction.spectrumComparisonLeftWhisker_constant
#check @SerrePositivity.KST.SConstruction.spectrumComparisonRightWhisker_constant
#print axioms SerrePositivity.KST.SConstruction.spectrumComparisonRightWhisker_constant
#check @SerrePositivity.KST.SConstruction.tracedWhiskerZeroSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedWhiskerZeroSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeFirstWhisker_zero_constant
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeFirstWhisker_zero_constant
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeSecondWhisker_zero_constant
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeSecondWhisker_zero_constant
#check @SerrePositivity.KST.SConstruction.monicKTracedNativeTriplePrescribedEdge_zero_constant
#print axioms SerrePositivity.KST.SConstruction.monicKTracedNativeTriplePrescribedEdge_zero_constant
#check @SerrePositivity.KST.SConstruction.CompositionDiamond.map
#print axioms SerrePositivity.KST.SConstruction.CompositionDiamond.map
#check @SerrePositivity.KST.SConstruction.CompositionDiamond.map_first_simplex
#print axioms SerrePositivity.KST.SConstruction.CompositionDiamond.map_first_simplex
#check @SerrePositivity.KST.SConstruction.CompositionDiamond.map_second_simplex
#print axioms SerrePositivity.KST.SConstruction.CompositionDiamond.map_second_simplex
#check @SerrePositivity.KST.SConstruction.CompositionDiamond.map_diagonal
#print axioms SerrePositivity.KST.SConstruction.CompositionDiamond.map_diagonal
#check @SerrePositivity.KST.SConstruction.tracedTripleZeroSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedTripleZeroSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleZeroEvaluation
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleZeroEvaluation
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleZeroDiamond
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleZeroDiamond
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleZeroLower_constant
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleZeroLower_constant
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleZeroFirstWhisker_constant
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleZeroFirstWhisker_constant
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleZeroSecondWhisker_constant
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleZeroSecondWhisker_constant
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleZeroPrescribed_constant
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleZeroPrescribed_constant
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleZeroComparison
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleZeroComparison
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleZeroComparisonRealization
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleZeroComparisonRealization
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleZeroComparisonRealization_comparison
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleZeroComparisonRealization_comparison
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleZeroComparisonRealization_first_triangle
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleZeroComparisonRealization_first_triangle
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleZeroComparisonRealization_second_triangle
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleZeroComparisonRealization_second_triangle
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleZeroComparisonRealization_relative
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleZeroComparisonRealization_relative
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleRawZeroComparison
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleRawZeroComparison
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleRawZeroComparison_h
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleRawZeroComparison_h
#check @SerrePositivity.KST.SConstruction.monicKTracedTripleRawZeroComparison_realization
#print axioms SerrePositivity.KST.SConstruction.monicKTracedTripleRawZeroComparison_realization
#check @SerrePositivity.KST.SConstruction.endpointFixedCylinderMapTransport
#print axioms SerrePositivity.KST.SConstruction.endpointFixedCylinderMapTransport
#check @SerrePositivity.KST.SConstruction.endpointFixedCylinderMapTransport_h
#print axioms SerrePositivity.KST.SConstruction.endpointFixedCylinderMapTransport_h
#check @SerrePositivity.KST.SConstruction.fixedBoundaryHomotopy_pullback
#print axioms SerrePositivity.KST.SConstruction.fixedBoundaryHomotopy_pullback
#check @SerrePositivity.KST.SConstruction.intervalParameterPoint
#print axioms SerrePositivity.KST.SConstruction.intervalParameterPoint
#check @SerrePositivity.KST.SConstruction.intervalParameterBoundaryPoint
#print axioms SerrePositivity.KST.SConstruction.intervalParameterBoundaryPoint
#check @SerrePositivity.KST.SConstruction.intervalParameterPoint_boundary
#print axioms SerrePositivity.KST.SConstruction.intervalParameterPoint_boundary
#check @SerrePositivity.KST.SConstruction.intervalParameterPoint_of_map
#print axioms SerrePositivity.KST.SConstruction.intervalParameterPoint_of_map
#check @SerrePositivity.KST.SConstruction.fixedBoundaryHomotopy_intervalPoint
#print axioms SerrePositivity.KST.SConstruction.fixedBoundaryHomotopy_intervalPoint
#check @SerrePositivity.KST.SConstruction.rawComparisonRectificationCorrection
#print axioms SerrePositivity.KST.SConstruction.rawComparisonRectificationCorrection
#check @SerrePositivity.KST.SConstruction.rawComparisonRectificationCorrection_h
#print axioms SerrePositivity.KST.SConstruction.rawComparisonRectificationCorrection_h
#check @SerrePositivity.KST.SConstruction.rawComparisonRectificationCorrection_boundary
#print axioms SerrePositivity.KST.SConstruction.rawComparisonRectificationCorrection_boundary
#check @SerrePositivity.KST.SConstruction.rawComparisonRectificationCorrection_zero
#print axioms SerrePositivity.KST.SConstruction.rawComparisonRectificationCorrection_zero
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeRawStageCorrection
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeRawStageCorrection
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeRawStageCorrection_h
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeRawStageCorrection_h
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeRawStageCorrection_boundary
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeRawStageCorrection_boundary
#check @SerrePositivity.KST.SConstruction.monicKPrismNativeRawStageCorrection_zero
#print axioms SerrePositivity.KST.SConstruction.monicKPrismNativeRawStageCorrection_zero
#check @SerrePositivity.KST.SConstruction.tracedCompositionStageSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedCompositionStageSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionIntervalPoint
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionIntervalPoint
#check @SerrePositivity.KST.SConstruction.monicKTracedSpectrumCompositionEdge_raw_evaluation
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSpectrumCompositionEdge_raw_evaluation
#check @SerrePositivity.KST.SConstruction.monicKTracedSpectrumCompositionEdge_corrected_evaluation
#print axioms SerrePositivity.KST.SConstruction.monicKTracedSpectrumCompositionEdge_corrected_evaluation
#check @SerrePositivity.KST.SConstruction.tracedStageCorrectionSpectrumSimplicialCategory
#print axioms SerrePositivity.KST.SConstruction.tracedStageCorrectionSpectrumSimplicialCategory
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionOriginalStage
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionOriginalStage
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionStageCorrection
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionStageCorrection
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionStageCorrection_h
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionStageCorrection_h
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionStageCorrection_relative
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionStageCorrection_relative
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionStageCorrection_source
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionStageCorrection_source
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionStageCorrection_target
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionStageCorrection_target
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionStageCorrection_zero
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionStageCorrection_zero
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionStageCorrection_zero_constant
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionStageCorrection_zero_constant
#check @SerrePositivity.KST.SConstruction.pointParameterMap
#print axioms SerrePositivity.KST.SConstruction.pointParameterMap
#check @SerrePositivity.KST.SConstruction.pointParameterMap_naturality
#print axioms SerrePositivity.KST.SConstruction.pointParameterMap_naturality
#check @SerrePositivity.KST.SConstruction.pointParameterMap_interval
#print axioms SerrePositivity.KST.SConstruction.pointParameterMap_interval
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionOriginalSpan
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionOriginalSpan
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionOriginalSpan_first
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionOriginalSpan_first
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionOriginalSpan_comparison
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionOriginalSpan_comparison
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionOriginalSpan_composite
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionOriginalSpan_composite
#check @SerrePositivity.KST.SConstruction.monicKTracedCompositionStageCorrection_span_source
#print axioms SerrePositivity.KST.SConstruction.monicKTracedCompositionStageCorrection_span_source
