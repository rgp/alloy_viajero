/*
			##########		 EL VIAJERO		 ############
	
	El problema a resolver es determinar un trayecto entre ciudades 
	el cual el viajero pueda recorrer sin pasar dos veces por la misma 
	ciudad y cuyo costo sea menor o igual al definido por el usuario.
	
	Se deben determinar los costos de viaje entre cada ciudad y 
	eventualmente también se debe poder definir el costo de viaje 
	entre todas las ciudades. El viajero debe poder llegar a todas 
	las ciudades y el trayecto propuesto no debe exceder el costo 
	determinado por el usuario. 

    El problema como tal dice:
        Se tiene un conjunto de ciudades que visitar por un viajero,
        que parte de una de esas ciudades.
        El problema es encontrar una secuencia de ciudades comunicadas,
        tales que el costo es a lo más un costo dado.
*/

//modulo para utilizar operaciones aritmeticas
module util/integer
//- Declaración para incluir la utilería de ordenamiento de Alloy
open util/ordering[PopulationState]

//- Código del estado del sistema para su proyecto, con comentarios explicando para qué sirve cada componente

/* Signatures */
one sig Viajero {
	origin: one Ciudad,
	destination: one Ciudad
}{
	origin != destination
}

abstract sig Ciudad {
	caminos: some Camino
}

one sig Ciudad1,Ciudad2,Ciudad3,Ciudad4,Ciudad5 extends Ciudad {}

sig Camino {
	a_city: one Ciudad,
	b_city: one Ciudad, // los caminos son reciprocos 
	//price : Int //es el precio de una ciudad a otra 
}{
	//price >= 0
	a_city != b_city
}

sig PopulationState {
	visiting: Viajero lone -> one Ciudad,
	//costoViaje: Viajero -> Int,
	visited: Viajero lone -> set Ciudad
/* Recomendación... un solo viajero */
}

/* EOSignatures */

fact todasLasCiudadesConectadas {
	some c:Ciudad,  r1,r2:Camino | r1 in c.caminos && r2 in c.caminos
}


fact caminosReciprocos {
	(a_city+b_city) = ~caminos
}


//- Fact con el estado inicial
fact initialState {
	first[].visiting = Viajero -> Viajero.origin
	first[].visited  = first[].visiting
}

//- Predicado con la operación para pasar de un estado al siguiente
pred Migrate(ps,ps': PopulationState, traveler: one Viajero, next: one Ciudad) { 
//####### PRECONDICIONES
// Que la siguiente ciudad no sea la misma ni se haya visitado previamente
next not in traveler.(ps.visited)
next != traveler.(ps.visiting)
//####### POSTCONDICIONES
//la ciudad siguiente es la visitada
ps'.visiting = (traveler -> next)
//####### MARCO DE REFERENCIA
ps'.visited = ps.visited + ps.visiting
}

//- Fact para el estado siguiente de un estado dado
fact transicionEstado {
	all hs:PopulationState,hs':next[hs] {
		some v:Viajero,c:Ciudad | Migrate[hs,hs',v,c]
	}
}

//- Predicado con la meta para que el sistema entregue una solución
pred resuelveViajero() {
	last[].visiting = Viajero -> Viajero.destination
}

run resuelveViajero for 5 expect 1
