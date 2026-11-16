use vstd::prelude::*;

verus! {

    // Constants -------------------------------------------------------

    // Compass headings indexed 0-8 and step by 45 degrees
    // 0 = N
    // 1 = NE
    // 2 = E
    // 3 = SE
    // 4 = S
    // 5 = SW
    // 6 = W
    // 7 = NW
    pub open spec fn num_compass_headings() -> int {
        8
    }

    // Altitude threshold for safety of flight (SOF)
    pub open spec fn min_altitude() -> int {
        5000
    }

    // State -----------------------------------------------------------
    pub struct FlightState {
        pub altitude: int,
        pub heading: int,  // compass index, see num_compass_headings()
        pub speed: int,
    }

    pub open spec fn flight_state_correct(s: FlightState) -> bool {
        &&& s.altitude >= min_altitude()
        &&& 0 <= s.heading < num_compass_headings()
        &&& s.speed >= 0 
    }

    // Initialize FlightState on ground, facing N, and stopped
    pub open spec fn init_state() -> FlightState {
        FlightState{ altitude: 0, heading: 0, speed: 0 }
    }

    pub proof fn init_flight_state_correct()
        ensures
            flight_state_correct(init_state()),
    {

    }

    mod stick {
        use vstd::prelude::*;
        use super::*;

        pub open spec fn move_up(s: FlightState, amount: int) -> FlightState
            requires
                amount > 0,
            // ensures 
            //     // TODO altitude increases 
        {
            // increase altitude in FlightState s
            FlightState { altitude: s.altitude + amount, heading: s.heading, speed: s.speed }
        }

        pub open spec fn move_down(s: FlightState, amount: int) -> FlightState
            requires
                amount > 0,
            // ensures 
            //     // TODO altitude decreases
            //     // TODO ensure altitude stays above threshold 
        {
            FlightState { altitude: s.altitude - amount, heading: s.heading, speed: s.speed }
        }

        pub open spec fn move_right(s: FlightState, steps: int) -> FlightState 
            requires
                steps > 0,
        {
            FlightState {
                altitude: s.altitude,
                heading: (s.heading + steps) % num_compass_headings(),
                speed: s.speed,
            }
        }

        pub open spec fn move_left(s: FlightState, steps: int) -> FlightState
            requires
                steps > 0,
        {
            FlightState {
                altitude: s.altitude,
                heading: (s.heading - steps) % num_compass_headings(),
                speed: s.speed,
            }
        }
    }

    mod throttle {
        use vstd::prelude::*;
        use super::*;

        pub open spec fn speed_up(s: FlightState, amount: int) -> FlightState
            requires
                amount > 0,
            // ensures 
            //     // TODO speed increases 
        {
            FlightState { altitude: s.altitude, heading: s.heading, speed: s.speed + amount }
        }

        pub open spec fn speed_down(s: FlightState, amount: int) -> FlightState
            requires
                amount > 0,
            // ensures 
            //     // TODO speed decreases
        {
            FlightState { altitude: s.altitude, heading: s.heading, speed: s.speed - amount }
        }
    }
}

fn main() {}